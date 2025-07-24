#!/usr/bin/env python
# coding: utf-8

# === Libraries ===
import os
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import train_test_split
from sklearn.utils.class_weight import compute_class_weight
from joblib import dump, load
import time

# === Custom Functions ===

def Index_EF(x):
    x['Time'] = pd.to_datetime(x['Time']).dt.floor('D')
    daily_mean = x.groupby('Time')['Daily_EF'].mean().reset_index()
    daily_mean.set_index('Time', inplace=True)

    daily_mean['Pre_pulse_EF'] = daily_mean['Daily_EF'].rolling(window=15, min_periods=10).mean().shift(2)
    daily_mean['Before_EF'] = daily_mean['Daily_EF'].rolling(window=2, min_periods=1).mean().shift(1)
    daily_mean['After_EF'] = daily_mean['Daily_EF'].rolling(window=2, min_periods=1).mean().shift(-1)
    daily_mean['Initial_EF'] = daily_mean['After_EF'] - daily_mean['Before_EF']

    x_final = pd.merge(x, daily_mean[['Initial_EF', 'Pre_pulse_EF', 'After_EF']], on='Time', how='outer').dropna()
    return x_final

def change_NEE(x):
    x['Time'] = pd.to_datetime(x['Time']).dt.floor('D')
    daily_mean = x.groupby('Time')['NEE_VUT_REF'].mean().reset_index()
    daily_mean.set_index('Time', inplace=True)

    daily_mean['Pre_pulse_NEE'] = daily_mean['NEE_VUT_REF'].rolling(window=3, min_periods=1).mean().shift(2)
    daily_mean['Before_NEE'] = daily_mean['NEE_VUT_REF'].rolling(window=2, min_periods=1).mean().shift(1)
    daily_mean['After_NEE'] = daily_mean['NEE_VUT_REF'].rolling(window=2, min_periods=1).mean().shift(-1)
    daily_mean['Initial_NEE'] = daily_mean['After_NEE'] - daily_mean['Before_NEE']
    daily_mean['Mean_NEE'] = daily_mean['NEE_VUT_REF']

    x_final = pd.merge(x, daily_mean[['Initial_NEE', 'Pre_pulse_NEE', 'Mean_NEE', 'After_NEE']], on='Time', how='outer').dropna()
    return x_final

def create_sop_eop_df(df):
    df['shifted'] = df['pulse_pred'].shift(1)
    df['next_shifted'] = df['pulse_pred'].shift(-1)
    df['change_start'] = (df['pulse_pred'] == 1) & (df['shifted'] != 1)
    df['change_end'] = (df['pulse_pred'] == 1) & (df['next_shifted'] != 1)

    df['SOP'] = df['Time'].where(df['change_start'])
    df['EOP'] = df['Time'].where(df['change_end'])

    sop_eop_df = pd.DataFrame({
        'SOP': df['SOP'].dropna().reset_index(drop=True),
        'EOP': df['EOP'].dropna().reset_index(drop=True)
    })
    sop_eop_df = sop_eop_df[sop_eop_df['SOP'] != sop_eop_df['EOP']]
    return sop_eop_df

def remove_bad_pulse(group):
    threshold = 0.5
    pulse_count = group['pulse_pred'].sum()
    group['pulse_pred'] = 1 if (pulse_count / group.shape[0]) > threshold else 0
    return group

# === Main Analysis ===

def main():
    # Set paths
    #combine data together
    #combine_df.csv is the combined .csv of all FluxPulse final products in 34 sites. Access the individual site data via ... and the combine_df.csv via ...:  
    
    data_path = "data/combined_df.csv"
    output_dir = "output"
    os.makedirs(output_dir, exist_ok=True)

    # Load and filter data
    combined_df = pd.read_csv(data_path)
    site_few = ['AU-Dry', 'AU-Gin', 'AU-Rig', 'US-FR2', 'US-xNG']
    site_few_BE = ['AU-Dry', 'US-xNG', 'AU-Gin', 'US-FR2', 'AU-DaS']

    combined_df_sub = combined_df[
        (combined_df["NEE_VUT_REF_QC"] == 0) &
        (~combined_df['Location'].isin(site_few)) &
        (~combined_df['Location'].isin(site_few_BE))
    ]

    features = ["Time_full", "Location", "Year", "Month", "Time", 'RECO_NT_VUT_REF', 
                "GPP_NT_VUT_REF", "NEE_VUT_REF", "Daily_EF", "P_ERA", "pulse_cluster"]
    combined_df_sub_fil = combined_df_sub[features].dropna()

    df_final = combined_df_sub_fil.groupby('Location').apply(Index_EF)
    df_final_NEE = combined_df_sub_fil.groupby('Location').apply(change_NEE)

    for col in ['Initial_NEE', 'Pre_pulse_NEE', 'Mean_NEE']:
        df_final[col] = df_final_NEE[col]

    df_final.reset_index(drop=True, inplace=True)
    df_encoded = df_final.drop(['Time_full', 'GPP_NT_VUT_REF'], axis=1)

    # Split by year per location
    latest_year_per_location = df_encoded.groupby('Location')['Year'].max()
    training_validating, testing_data = pd.DataFrame(), pd.DataFrame()

    for location, latest_year in latest_year_per_location.items():
        train_data = df_encoded[(df_encoded['Location'] == location) & (df_encoded['Year'] < latest_year - 2)]
        test_data = df_encoded[(df_encoded['Location'] == location) & (df_encoded['Year'].isin([latest_year, latest_year - 1, latest_year - 2]))]
        training_validating = pd.concat([training_validating, train_data])
        testing_data = pd.concat([testing_data, test_data])

    # Balance training data
    zero_rows = training_validating[training_validating['pulse_cluster'] == 0]
    retained_zero_rows = zero_rows.sample(frac=0.3, random_state=42)
    non_zero_rows = training_validating[training_validating['pulse_cluster'] != 0]
    training_validating = pd.concat([retained_zero_rows, non_zero_rows])

    # Split features and labels
    X_train_valid = training_validating.drop(['Location', 'pulse_cluster', 'Year', 'Time'], axis=1).to_numpy()
    y_train_valid = training_validating['pulse_cluster'].to_numpy()
    X_train, X_valid, y_train, y_valid = train_test_split(X_train_valid, y_train_valid, stratify=y_train_valid)

    # Train classifier
    start_time = time.time()
    class_weights = compute_class_weight(class_weight='balanced', classes=np.unique(y_train), y=y_train)
    weights = {i: class_weights[i] for i in range(len(class_weights))}

    classifier_full = RandomForestClassifier(random_state=100, class_weight=weights)
    classifier_full.fit(X_train, y_train)
    y_pred = classifier_full.predict(X_valid)

    print(f"Validation accuracy: {np.mean(y_pred == y_valid):.2f}")
    print(f"Training runtime: {time.time() - start_time:.2f} seconds")

    # Predict on test set
    df_all = []
    for location in df_encoded['Location'].unique():
        data_sub = testing_data[testing_data['Location'] == location]
        X_test = data_sub.drop(['Location', 'pulse_cluster', 'Year', 'Time'], axis=1).to_numpy()
        data_sub['pulse_pred'] = classifier_full.predict(X_test)
        df_all.append(data_sub)

    # Detect SOP/EOP
    ML_detect = []
    for df_sub in df_all:
        df_sub = df_sub.reset_index(drop=True)
        sop_eop = create_sop_eop_df(df_sub.groupby('Time').apply(remove_bad_pulse))
        sop_eop['SITE_ID'] = df_sub['Location'].iloc[0]
        ML_detect.append(sop_eop)

    ML_detect_merge = pd.concat(ML_detect, ignore_index=True)
    ML_detect_merge.to_csv(os.path.join(output_dir, "ML_detect.csv"), index=False)

    # Feature importance
    feature_names = training_validating.drop(['Location', 'pulse_cluster', 'Year', 'Time'], axis=1).columns
    importance_scores = sorted(zip(feature_names, classifier_full.feature_importances_), key=lambda x: x[1], reverse=True)
    pd.DataFrame(importance_scores, columns=['Feature', 'Importance']).to_csv(os.path.join(output_dir, "feature_scores.csv"), index=False)

    print("Pipeline completed successfully.")

if __name__ == "__main__":
    main()
