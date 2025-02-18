##Develop function to format the time column
#Requirements: Add 6 columns of Time_full (YYYY-MM-DD-HH-MM-SS), Time (YYYY-MM-DD), DOY, Hour, Month, Year. All are in form of POSIXct or numeric
#####
#Calling libraries
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
##Spectral Cluster and K-mean 
library("kernlab")
library(scales)
library(plotly)
library(ggfortify)
library(cluster)
#Single Spectrum Analysis
library(Rssa)
library(lattice)
library(latticeExtra)
library(fma)
##Functions for propensity score
library(MatchIt)
##Function for correlation and PCA
library(corrr)
library(ggcorrplot)
library("FactoMineR")
library("factoextra")
library(relaimpo)
#####
###Spectral Clustering Functions
time_convert <- function(df) {
  df$Time_full <-  BerkeleyJulianDateToPOSIXct(df$TIMESTAMP_END)
  df$Time <- as.Date(format(df$Time_full, "%Y-%m-%d"))
  df$DOY <- as.numeric(format(df$Time_full, "%j"))
  df$Hour <- as.numeric(format(df$Time_full, "%H")) + as.numeric(format(df$Time_full, "%M"))/60 
  df$Month <- as.numeric(format(df$Time_full, "%m"))
  df$Year <- as.numeric(format(df$Time_full,"%Y"))
  return(df)
}


##Develop function to calculate daily EF. Using variable name "LE_F_MDS" and H_F_MDS. Filter for original, positive, and dat-time LE and H. Calculate mean EF during day-time and copy it to all hour during the day
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

EF_change_rate <- function(df) {
  df$EF_rate <- df$Daily_EF
  for(i in 2:nrow(df)) {
    df$EF_rate[i] <- (df$Daily_EF[i] -  df$Daily_EF[i-1])/df$Daily_EF[i-1]
  }
  return(df)
}

NEE_change_rate <- function(df) {
  df$NEE_rate <- df$Daily_NEE
  for(i in 2:nrow(df)) {
    df$NEE_rate[i] <- (df$Daily_NEE[i] -  df$Daily_NEE[i-1])/df$Daily_NEE[i-1]
  }
  return(df)
}

##Calculating Total_Randunc column
sum_sqrt <- function(array) {
  return (sqrt(sum(array^2))/length(array))
  
}

#normalizing min/max function
minMax <- function(x) {
  return((x - min(x)) / (max(x) - min(x)))
}


total_Randunc_df <- function(df) {
  Total_Randunc_df <- df %>% group_by(Time) %>% 
    summarise(across(NEE_VUT_REF_RANDUNC, sum_sqrt))
  colnames(Total_Randunc_df) <- c("Time", "Total_Randunc")
  Total_Randunc_df$Time <- as.Date(Total_Randunc_df$Time)
  return(Total_Randunc_df)
}

##Putting night time data and early morning data to be on the same date (instead of different date)
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

##Obtaining training dataset
##Filter for Night-time data only
##Filter NT data that matches the QC for important variables
##Filter 5% and 95% of Night-time data
train_df <- function(df) {
  df_sub <- subset(df, NEE_VUT_REF_QC == 0 & NIGHT == 1 & RECO_NT_VUT_REF > -9999 & TS_F_MDS_1_QC == 0)
  return(df_sub)
}

##Create daily aggregated dataset for all files
##If the day does not have more than 5 data points, eliminate this day
daily_df <- function(df) {
  df <- df %>% group_by(Time) %>%  filter(n() >= 3) %>%
    summarise(across(c(Month, NEE_VUT_REF, RECO_NT_ori, RECO_NT_VUT_REF), mean))
  return(df)
}

quality_flag <- function(df) {
  df_count_all <- subset(df, NIGHT ==1) %>% count("Time")
  df_sub <- subset(df, NEE_VUT_REF_QC == 0 & NIGHT == 1 & RECO_NT_VUT_REF > -9999)
  df_count_night <- df_sub %>% count("Time")
  df_merge <- list(df_count_all, df_count_night) %>% reduce(inner_join, by = "Time")
  colnames(df_merge) <- c("Time", "n_all", "n_sub")
  df_merge$QC <- df_merge$n_sub/df_merge$n_all
  df_new <- df_merge[, c("Time", "QC", "n_all", "n_sub")]
  df_new$Time <- as.Date(df_new$Time)
  return(df_new)
}

daily_P_df <- function(df) {
  df_P <- aggregate(P_ERA ~ Time, data = df, mean)
  colnames(df_P) <- c("Time", "Daily_P")
  df_P$Time <- as.Date(df_P$Time)
  return(df_P)
}
##Format df to put into spectral clustering
##Columns needed: "Daily_resi_temp", "Daily_EF", "Daily_P", "Total_Randunc", "Daily_NEE", "Daily_RECO_temp"
reformat_for_clustering <- function(df, EF_df, Daily_P_df, Total_Randunc_df) {
  #Rename existing columns
  df <- rename(df, Daily_NEE = "NEE_VUT_REF", Daily_RECO_temp = "RECO_NT_ori", Daily_RECO_flux = "RECO_NT_VUT_REF")
  #Add Residual columns
  df$Daily_resi_temp <- df$Daily_NEE - df$Daily_RECO_temp
  df$Daily_resi_flux <- df$Daily_NEE - df$Daily_RECO_flux
  #Add Total_Randunc and Daily_EF
  df_list <- list(df[, c("Time", "Month", "Daily_NEE", "Daily_RECO_temp", "Daily_RECO_flux", "Daily_resi_temp", "Daily_resi_flux")], 
                  EF_df, Daily_P_df, Total_Randunc_df)
  df_list <- df_list %>% reduce(inner_join, by = "Time")
  #Add year column
  df_list$Year <- as.numeric(format(as.Date(df_list$Time), "%Y"))
  #Remove where Randunc > 100
  df_list <- subset(df_list, Total_Randunc < 100)
  return(df_list)
}

##pulse_correction will return data frame with corrected Reco and cluster decision. Cluster results are run 100 times and chosen based on three criteria: 
#all positive resi values, more than 2 points in the clusters, and has the highest rsq among the qualified ones.
pulse_correction <- function(df, iteration) {
  ##set up array containing cluster results
  rsq <- c()
  cluster_number_list <- c()
  df_list <- list()
  tryCatch(
    #Run spectral clustering for iteration times
    for(j in 1:iteration) {
      #Normalize variables
      #df_specc <- as.matrix(as.data.frame(lapply(df[, c("Daily_resi_temp", "Daily_EF", "Daily_P")], minMax)))
      df_specc <- as.matrix(df[, c("Daily_resi_temp", "Daily_EF", "Daily_P")])
      cluster_run <- specc(df_specc, 3)
      clustered_defined_df <- df %>% add_column(cluster = factor(cluster_run))
      #Select cluster in which 60% points are positive values only
      cluster_number <- NA
      cluster_number_positive <- NA
      for(i in 1:3) {
        df_positive <- subset(clustered_defined_df, cluster == i & Daily_resi_temp > 0)
        df_cluster <- subset(clustered_defined_df, cluster == i)
      #choose the cluster that contains the highest points
        max_resi <- max(clustered_defined_df$Daily_resi_temp)
        cluster_max <- clustered_defined_df$cluster[which(clustered_defined_df$Daily_resi_temp == max_resi)]
        if(nrow(df_positive) > 0.6*nrow(df_cluster)) {
          cluster_number_positive = i
          if(cluster_number_positive == cluster_max) {
            cluster_number = cluster_number_positive
          } else {
            print("Cluster chosen does not have the max value")
          }
        } else {
          print("Cluster identified has more than 40% negative values")
        }
      }
      #Select points that passes the random uncertainty test for that cluster
      cluster_chosen_df <- subset(clustered_defined_df, cluster == cluster_number & Daily_resi_temp > Total_Randunc)
      #Check if the cluster has more than 2 points
      if(nrow(cluster_chosen_df) > 2) {
        #Derive linear function for the selected cluster
        cluster_chosen_df_lm <- lm(Daily_resi_temp ~ Daily_EF, data = cluster_chosen_df)
        #Calculating RECO based on cluster regression 
        index_cluster <- which(clustered_defined_df$cluster == cluster_number & (clustered_defined_df$Daily_resi_temp > clustered_defined_df$Total_Randunc))
        clustered_defined_df$predicted_RECO <- clustered_defined_df$Daily_RECO_temp
        for(k in 1:nrow(clustered_defined_df)) {
          if(k %in% index_cluster) {
            clustered_defined_df$predicted_RECO[k] <- clustered_defined_df$Daily_RECO_temp[k] + cluster_chosen_df_lm$coefficients[1] +
              cluster_chosen_df_lm$coefficients[2]*clustered_defined_df$Daily_EF[k]
          }
        }
        #Calculating rsq for each cluster run
        rsq_j <- rsq(clustered_defined_df, Daily_NEE, predicted_RECO)[,3]
        rsq[j] <- rsq_j
        cluster_number_list[j] <- cluster_number
        df_list[[j]] <- clustered_defined_df
      } else {
        print("not enough points in the cluster")}
    },
    error = function(e) {
      df_list = data.frame()
    }
  )
  #Choose the cluster with the highest rsq. Returning in the following order: 
  #[1] data frame with cluster information. 
  #[2] highest rsq from all cluster
  #[3] the index of the cluster that been categorized as pulse 
  #[4] intercept for the lm function fitted through the pulse cluster
  #[5] slope for the lm function fitted through the pulse cluster
  #[6] squared of the fitted lm
  #[7] p-value of the fitted lm
  rsq_unlist <- array(as.numeric(unlist(rsq)))
  cluster_number_unlist <- array(as.numeric(unlist(cluster_number_list)))
  max_sort <- sort(rsq_unlist, index.return = TRUE, decreasing = TRUE)
  max_index <- max_sort$ix[1]
  cluster_df_final <- data.frame(df_list[max_index])
  if(nrow(cluster_df_final) == 0) {
    return(NULL)
  } else{
    return(list(cluster_df_final, max_sort$x[1], cluster_number_unlist[max_index], cluster_chosen_df_lm$coefficients[1], cluster_chosen_df_lm$coefficients[2], summary(cluster_chosen_df_lm)$r.squared,  lmp(cluster_chosen_df_lm)))
  }
}

##create a function to run cluster on customized window
cluster_fix_interval <- function(df, iteration, ini_step, end_step) {
  df_new <- df[ini_step:end_step,]
  df_cluster <- pulse_correction(df_new, iteration)
  return(df_cluster)
}

####################
##Temperature Regresison Functions 
##Set initial parameter/constant values
Tref = 288.15
T0 = 227.13
CtoK = 273.15
E0_max = 450
E0_min = 0

##Non-linear regression function for Initial Temperature sensitivity (window selection, temp limit, min point required)
##E0 supposed to be constant, if ever change, will change over time due to plant adaptation strategies but not due to temperature change
##Rules for choosing valid E0 (E0 < 0 -> = 0, E0 > 450 -> = 450)
##Estimate short-term E0 with the value K estimated above
#create an array of window
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

E0_calculation <- function(df) {
  df$E0_collection[which(df$E0_collection < 0)] <- 0
  df$E0_collection[which(df$E0_collection > E0_max)] <- E0_max
  ##Selection from the literature (Reichstein et al, 2005)
  df <- subset(df , E0_collection > E0_min & E0_collection < E0_max & E0_RSE/E0_collection < 0.5)
  E0_short_term <- mean(df$E0_collection)
  return(E0_short_term)
}

##Non-linear regression using fixed E0 and b. estimating a changing for every 4 days
centroid_day <- function(df, i) {
  max_point = max(length(which(df$Time == as.Date(i))), length(which(df$Time == as.Date(i + 1))), length(which(df$Time == as.Date(i + 2))), length(which(df$Time == as.Date(i + 3))))
  for(i in as.list(unique(df$Time))) {
    if(length(which(df$Time == as.Date(i))) == max_point) {
      df_sub <- subset(df, Time == as.Date(i))
      return(df_sub$Time_full[1])
    }
  }
}

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
      #time <- test_loop[nrow(test_loop), "Time_full"]
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

RECO_estimation <- function(df, E0) {
  df$RECO_NT_ori <- exp(E0 * (1/(Tref - T0) - 1/(df$TA_F_MDS  + CtoK - T0)))*(df$R0_interpolated)
  return(df)
}

lmp <- function (modelobject) {
  if (class(modelobject) != "lm") stop("Not an object of class 'lm' ")
  f <- summary(modelobject)$fstatistic
  p <- pf(f[1],f[2],f[3],lower.tail=F)
  attributes(p) <- NULL
  return(p)
}

My_Theme = theme(
  axis.title.x = element_text(size = 16),
  axis.text.x = element_text(size = 20),
  axis.title.y = element_text(size = 16))

envi_corr <- function(var, df) {
  df <- df[, c("slope_pulse_list", "slope_list", var)]
  #calculate stat of linear regression
  lm_pulse <- lm(df$slope_pulse_list ~ df[, 3])
  lm_non_pulse <- lm(df$slope_list ~ df[, 3])
  rsq_pulse <- summary(lm_pulse)$r.squared
  rsq_non_pulse <- summary(lm_non_pulse)$r.squared
  slope_pulse <- summary(lm_pulse)$coefficients[2]
  slope_non_pulse <- summary(lm_non_pulse)$coefficients[2]
  p_pulse <- lmp(lm_pulse)
  p_non_pulse <- lmp(lm_non_pulse)
  stat_pulse <- paste("Pulse: slope = ", round(slope_pulse, 2), ", R2 = ", round(rsq_pulse, 2), ", p = ", round(p_pulse, 3), sep = "")
  stat_non_pulse <- paste("Non-pulse: slope = ", round(slope_non_pulse, 2), ", R2 = ", round(rsq_non_pulse, 2), ", p = ", round(p_non_pulse, 3), sep = "")
  graph <- ggplot(df, aes(x = df[,3])) + 
    theme_bw() + 
    geom_smooth(aes(y = slope_pulse_list), method = "lm", color = "blue", fill = "blue") + 
    geom_smooth(aes(y = slope_list), method = "lm", color = "orange", fill = "orange") +
    geom_point(aes(y = slope_list), color = "orange") +
    geom_point(aes(y = slope_pulse_list), color = "blue") +
    ylab("Pulse intensity") +
    xlab(var) + 
    labs(subtitle = paste(stat_pulse, "\n", stat_non_pulse, sep = "")) +
    theme(axis.text=element_text(size = 10), text = element_text(size = 11))
  return(graph)
}

envi_corr_prop <- function(var, df) {
  df <- df[, c("slope_prop_list", var)]
  #calculate stat of linear regression
  lm_prop <- lm(df$slope_prop_list ~ df[, 2])
  rsq_prop <- summary(lm_prop)$r.squared
  slope_prop <- summary(lm_prop)$coefficients[2]
  p_prop <- lmp(lm_prop)
  stat_prop <- paste("Slope = ", round(slope_pulse, 2), ", R2 = ", round(rsq_prop, 2), ", p = ", round(p_prop, 3), sep = "")
  graph <- ggplot(df, aes(x = df[,2])) + 
    theme_bw() + 
    geom_smooth(aes(y = slope_prop_list), method = "lm", color = "blue", fill = "blue") + 
    geom_point(aes(y = slope_prop_list), color = "blue") +
    ylab("delta(NEE)-Delta(EF) Slope") +
    xlab(var) + 
    labs(subtitle = paste(stat_prop)) +
    theme(axis.text=element_text(size = 10), text = element_text(size = 11))
  return(graph)
}

##Temperature regression function 
temp_regression_full <- function(dir) {
  df <- read.csv(dir)
  df <- time_convert(df)
  #Run temperature regression
  site_train <- subset(train_df(df), TS_F_MDS_1_QC == 0)
  ##Run temp-regression
  E0_df <- temp_regression(site_train, 14, 5)
  E0 <- E0_calculation(E0_df)
  R0_df <- R0_regression(site_train, E0, 4, 0)
  R0_interpolated <- R0_interpolate(df, R0_df)
  RECO_df <- RECO_estimation(R0_interpolated, E0)
  return(RECO_df)
}

##Prepare dataset to pass into Spectral Clustering
spectral_clustering_prep <- function(df) {
  ##Group Night-time data from 2 adjacent days
  #df_time_adj <- time_adjust(df)
  ##adding quality flag
  df$Time <- as.Date(df$Time)
  df_QC <- quality_flag(df)
  
  ##Average GPP, TS, TA, P_F,POT SW, LE, H, SWC
  df_TS <- subset(df, TS_F_MDS_1_QC == 0 & NIGHT == 1)
  df_TS <- aggregate(TS_F_MDS_1 ~ Time, data = df_TS, mean)
  
  df_TA <- subset(df, TA_F_MDS_QC == 0 & NIGHT == 1)
  df_TA <- aggregate(TA_F_MDS ~ Time, data = df_TA, mean)
  
  df_GPP <- subset(df, GPP_DT_VUT_REF > -9999)
  df_GPP <- aggregate(GPP_DT_VUT_REF ~ Time, data = df_GPP, mean)
  
  df_P <- subset(df, P_F_QC < 2)
  df_P <- aggregate(P_F ~ Time, data = df_P, mean)
  
  df_NEE <- subset(df, NIGHT == 0)
  df_NEE <- aggregate(NEE_VUT_REF ~ Time, data = df_NEE, mean)
  
  df_SW <- aggregate(SW_IN_POT ~ Time, data = df, mean)
  
  if(length(which(df$LE_F_MDS_QC == 0)) > 100 | length(which(df$H_F_MDS_QC == 0)) > 100) {
    df_sub_LE_H <- subset(df, LE_F_MDS_QC == 0 & H_F_MDS_QC == 0 & NIGHT != 1 & H_F_MDS > 0 & LE_F_MDS > 0)
    df_LE <- aggregate(LE_F_MDS ~ Time, data = df_sub_LE_H, mean)
    df_H <- aggregate(H_F_MDS ~ Time, data = df_sub_LE_H, mean)
  }

  df_mean_merge <- list(df_QC, df_TS, df_TA, df_GPP, df_NEE, df_P, df_SW, df_LE, df_H) %>% reduce(full_join, by = "Time")
  colnames(df_mean_merge) <- c("Time", "QC", "n_all", "n_sub", "Daily_TS", "Daily_TA", "Daily_GPP", "Daytime_NEE",
                               "Daily_P_site", "Daily_POT_SW",
                               "Daytime_LE", "Daytime_H")
  df_mean_merge$Time <- as.Date(df_mean_merge$Time)
  ##Aggregate df on daily scale 
  train_data <- train_df(df)
  daily_train_df <- daily_df(train_data)
  ##Derive Daytime_EF and Total_Randunc data frame
  Daytime_EF_df <- daytimeEF_df(df)
  Daily_P_df <- daily_P_df(df)
  Total_Randunc_df <- total_Randunc_df(df)
  #merge daily_train_df with EF and Randunc
  df_cluster_train <- reformat_for_clustering(daily_train_df, Daytime_EF_df, Daily_P_df, Total_Randunc_df)
  df_cluster_train_final <- list(df_cluster_train, df_mean_merge) %>% reduce(inner_join, by = "Time")
  return(df_cluster_train_final)
}




