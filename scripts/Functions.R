# ------------------------------------------------------------------------------
# Calling libraries
# ------------------------------------------------------------------------------
library(REddyProc)
library(dplyr)
library(ggplot2)
library(reshape2)
library(purrr)
library(runner)
library(minpack.lm)
require(lubridate)
library(zoo)
library(gridExtra)
library(ggrepel)
library(astsa, quietly=TRUE, warn.conflicts=FALSE)
library(knitr)
library(plyr)
library(TTR)
library(tidyverse)
library(timetk)
library(tidyquant)
library(yardstick)
library(xts)
library(hexbin)
library(RColorBrewer)
library(gridExtra)
library(ggrepel)
options(ggrepel.max.overlaps = Inf)
library(scales)
library(ppcor)
# ------------------------------------------------------------------------------
# Function for correlation and PCA
# ------------------------------------------------------------------------------
library(corrr)
library(ggcorrplot)
library("FactoMineR")
library("factoextra")
library(relaimpo)
# ------------------------------------------------------------------------------
# Load parallel backends
# ------------------------------------------------------------------------------
library(foreach)
library(doParallel)
# ------------------------------------------------------------------------------
# Configuration library
# ------------------------------------------------------------------------------
library(yaml)
# ------------------------------------------------------------------------------
# Customize quantile functions
# ------------------------------------------------------------------------------
quantile_98 <- function(x) {
  # Return 98th percentile of x
  return(quantile(x, 0.98))
}
median_na_rm <- function(x) {
  # Return median of x, removing NA
  return(median(x, na.rm = TRUE))
}
quantile_68 <- function(x) {
  # Return 68th percentile of x
  return(quantile(x, 0.68))
}
# ------------------------------------------------------------------------------
# Register the parallel backend with one fewer than all available cores
# ------------------------------------------------------------------------------
no_cores <- detectCores() - 1
registerDoParallel(cores = no_cores)



# ------------------------------------------------------------------------------
# Convert FLUXNET-formatted time columns
# ------------------------------------------------------------------------------
time_convert <- function(df) {
  df$Time_full <-  BerkeleyJulianDateToPOSIXct(df$TIMESTAMP_END)
  df$Time <- as.Date(format(df$Time_full, "%Y-%m-%d"))
  df$DOY <- as.numeric(format(df$Time_full, "%j"))
  df$Hour <- as.numeric(format(df$Time_full, "%H")) + as.numeric(format(df$Time_full, "%M"))/60 
  df$Month <- as.numeric(format(df$Time_full, "%m"))
  df$Year <- as.numeric(format(df$Time_full,"%Y"))
  return(df)
}


# ------------------------------------------------------------------------------
#Adjust the time (or date) column to make sure that the date starts from sunrise to sunset, instead of from midnight to midnight.
#The reason for doing that is to make sure EF is calculated for the full day before the night, not the day 'between' the night.
# ------------------------------------------------------------------------------
time_adjust <- function(df) {
  df$Time <- as.Date(df$Time)
  df$Time_adj <- df$Time
  for(i in 1:length(unique(df$Time))) {
    if(!is.na(unique(df$Time)[i + 1])) {
      if(unique(df$Time)[i + 1] - unique(df$Time)[i] == 1) {
        index_morning <- which(df$NIGHT == 1 & df$Hour < 12 & df$Time == unique(df$Time)[i+1])
        df$Time_adj[index_morning] <- unique(df$Time)[i]
      }
    }
  }
  ini_index_morning <- which(df$Time == unique(df$Time)[1] & df$Hour < 12 & df$NIGHT == 1)
  df$Time_adj[ini_index_morning] <- unique(df$Time)[1] - 1
  df$Time <- df$Time_adj
  return(df)
}


# ------------------------------------------------------------------------------
# Calculate daily EF. Using variable name "LE_F_MDS" and "H_F_MDS." Filter for original, positive, and daytime LE and H. 
# Calculate mean EF during day-time and copy it to all hour during the day
# ------------------------------------------------------------------------------
daytimeEF_df <- function(df) {
  #If there are more than 100 points of original H and LE data, use the original data
  if(length(which(df$LE_F_MDS_QC == 0)) > 100 | length(which(df$H_F_MDS_QC == 0)) > 100) {
    df_sub <- subset(df, LE_F_MDS_QC == 0 & H_F_MDS_QC == 0 & NIGHT != 1 & H_F_MDS > 0 & LE_F_MDS > 0)
    df_sub$EF <- df_sub$LE_F_MDS/(df_sub$LE_F_MDS + df_sub$H_F_MDS)
    df_EF <- aggregate(EF ~ Time, data = df_sub, mean)
    colnames(df_EF) <- c("Time", "Daily_EF")
    df_EF$Time <- as.Date(df_EF$Time)
    return(df_EF)
  }
  #If there are fewer than 100 original H and LE data, use the gap-filled LE and H
  else {
    df_sub <- subset(df, NIGHT != 1 & H_F_MDS > 0 & LE_F_MDS > 0)
    df_sub$EF <- df_sub$LE_F_MDS/(df_sub$LE_F_MDS + df_sub$H_F_MDS)
    df_EF <- aggregate(EF ~ Time, data = df_sub, mean)
    colnames(df_EF) <- c("Time", "Daily_EF")
    df_EF$Time <- as.Date(df_EF$Time)
    return(df_EF)
  }
}

# ------------------------------------------------------------------------------
# ------------------------------------------------------------------------------
# Replicate Nighttime partitioning method
# ------------------------------------------------------------------------------
# ------------------------------------------------------------------------------


# ------------------------------------------------------------------------------
# Obtaining training dataset by Filter for original (QC == 0) and Night-time data only
# ------------------------------------------------------------------------------
train_df <- function(df) {
  df_sub <- subset(df, NEE_VUT_REF_QC == 0 & NIGHT == 1 & RECO_NT_VUT_REF > -9999 & TS_F_MDS_1_QC == 0)
  return(df_sub)
}

# ------------------------------------------------------------------------------
# Temperature Regression function to estimate temperature sensitivity, allowing customizing window length
# ------------------------------------------------------------------------------
# Set initial parameter/constant values
Tref = 288.15
T0 = 227.13
CtoK = 273.15
E0_max = 450
E0_min = 0

# Function temp_regression() return the dataset of temperature sensitivity for each rolling window
temp_regression <- function(df, win_len, overlap_len) {
  E0_collection <- c()
  E0_RSE <- c()
  E0_date <- c()
  date_list <- seq(as.Date(unique(df$Time)[1]),
                   as.Date(unique(df$Time)[length(unique(df$Time))]), 
                   by = (win_len - overlap_len))
  for( i in as.list(date_list)) {
    test_loop = subset(df, (as.Date(Time) >= i) & (as.Date(Time) <= i + days(win_len - 1)))
    if(nrow(test_loop) >= 6) { #Only choose window with >= 6 points and temp range >= 5C
      temp_range = max(test_loop$TS_F_MDS_1) - min(test_loop$TS_F_MDS_1)
      if(temp_range >= 5) {
        try({
          regression_nls <- nls(NEE_VUT_REF ~ R0*exp(E0 * (1/(Tref - T0) - 1/(TS_F_MDS_1 + CtoK - T0))),
                                data = test_loop, control = nls.control(warnOnly = TRUE), start = list(R0 = 1, E0 = 100))
          if(is.numeric(summary(regression_nls)$parameters["E0",2])) {
            E0_RSE <- append(E0_RSE, summary(regression_nls)$parameters["E0",2])
            E0_date <- append(E0_date, i + days(win_len - 1))
            E0_collection <- append(E0_collection, coef(regression_nls)[2])
          } else {print("produce NA of E0")}
        })
      } else {print("temp range < 5")} 
    } else {print("window < 6 points")}
  }
  E0_collection <- as.data.frame(E0_collection)
  E0_RSE <- as.data.frame(E0_RSE)
  E0_date <- as.data.frame(E0_date)
  E0_data_notFiltered <- data.frame(E0_collection, E0_RSE, E0_date)
  return(E0_data_notFiltered)
}

# ------------------------------------------------------------------------------
# From the datasets of temperature sensitivity obtained above (E0), calculating constant E0 for the whole site
# ------------------------------------------------------------------------------
E0_calculation <- function(df) {
  df$E0_collection[which(df$E0_collection < 0)] <- 0
  df$E0_collection[which(df$E0_collection > E0_max)] <- E0_max
  ##Selection from the literature (Reichstein et al, 2005)
  df <- subset(df , E0_collection > E0_min & E0_collection < E0_max & E0_RSE/E0_collection < 0.5)
  E0_short_term <- mean(df$E0_collection)
  return(E0_short_term)
}

# ------------------------------------------------------------------------------
# Create function centroid_day() to determine the central day of a moving window (used in the later function of calculating Reference Respiration (R0))
# ------------------------------------------------------------------------------
centroid_day <- function(df, i) {
  max_point = max(length(which(df$Time == as.Date(i))), length(which(df$Time == as.Date(i + 1))), length(which(df$Time == as.Date(i + 2))), length(which(df$Time == as.Date(i + 3))))
  for(i in as.list(unique(df$Time))) {
    if(length(which(df$Time == as.Date(i))) == max_point) {
      df_sub <- subset(df, Time == as.Date(i))
      return(df_sub$Time_full[1])
    }
  }
}

# ------------------------------------------------------------------------------
# Calculating Reference Respiration (R0) using a customized moving window, following methods described in Reichstein et al., 2005
# ------------------------------------------------------------------------------
R0_regression <- function(df, E0, win_len, overlap_len) {
  R0_collection <- c()
  R0_RSE <- c()
  R0_date <- c()
  date_list <- seq(as.Date(unique(df$Time)[1]),
                   as.Date(unique(df$Time)[length(unique(df$Time))]), 
                   by = win_len - overlap_len)
  for( i in as.list(date_list)) {
    test_loop = subset(df, as.Date(Time) >= i & as.Date(Time) <= i + days(win_len - 1))
    if(nrow(test_loop) >= 2) {
      time <- centroid_day(test_loop, i)
      try({
        regression_nls <- nls(NEE_VUT_REF ~ exp(E0 * (1/(Tref - T0) - 1/(TS_F_MDS_1 + CtoK - T0)))*R0,
                              data = test_loop, control = nls.control(warnOnly = TRUE), start = list(R0 = 1))
        if(is.numeric(summary(regression_nls)$parameters["R0",2])) {
          R0_RSE <- append(R0_RSE, summary(regression_nls)$parameters["R0",2])
          R0_collection <- append(R0_collection, coef(regression_nls)[1])
          R0_date <- append(R0_date, time)
        } else {print("regression failed")}
      })
    } else {print("less than 6 points available")}
  }
  R0_collection <- as.data.frame(R0_collection)
  R0_RSE <- as.data.frame(R0_RSE)
  R0_date <- as.data.frame(R0_date)
  R0_df <- data.frame(R0_collection, R0_RSE, R0_date)
  return(R0_df)
}

# ------------------------------------------------------------------------------
# Interpolate Reference Respiration (R0)
# ------------------------------------------------------------------------------
R0_interpolate <- function(df, R0_df) {
  colnames(R0_df) <- c("R0_original", "R0_RSE", "Time_full")
  R0_df$R0_original[which(R0_df$R0_original < 10**-6)] <- 10**-6
  R0_merged <- merge(R0_df, df, all = TRUE, by = "Time_full")
  # Deleting initial and ending NA value of R0
  index <- which(!is.na(R0_merged$R0_original))
  R0_merged_filter <- R0_merged[index[1]:index[length(index)], ]
  #Linear Interpolation for NA R0
  R0_interpolated <- data.frame(na.approx(R0_merged_filter$R0_original))
  R0_interpolated_df <- data.frame(R0_interpolated, R0_merged_filter)
  colnames(R0_interpolated_df)[1] <- "R0_interpolated"
  return(R0_interpolated_df)
}

# ------------------------------------------------------------------------------
# Estimate Ecosystem Respiration and save it as variable "RECO_NT_ori", which means the "original Nighttime Method RECO"
# ------------------------------------------------------------------------------
RECO_estimation <- function(df, E0) {
  df$RECO_NT_ori <- exp(E0 * (1/(Tref - T0) - 1/(df$TA_F_MDS  + CtoK - T0)))*(df$R0_interpolated)
  return(df)
}

# ------------------------------------------------------------------------------
# Extract p-value from a linear regression model
# ------------------------------------------------------------------------------
lmp <- function (modelobject) {
  if (class(modelobject) != "lm") stop("Not an object of class 'lm' ")
  f <- summary(modelobject)$fstatistic
  p <- pf(f[1],f[2],f[3],lower.tail=F)
  attributes(p) <- NULL
  return(p)
}

# ------------------------------------------------------------------------------
# Define ggplot theme for plot visualization
# ------------------------------------------------------------------------------
My_Theme = theme(
  axis.title.x = element_text(size = 16),
  axis.text.x = element_text(size = 20),
  axis.title.y = element_text(size = 16))





