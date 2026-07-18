# FILENAME: paper/proton-radius/analysis.py

import numpy as np
from scipy.optimize import curve_fit

# -----------------------------------------------------------------------------
# 1. JLab GEp Polarization Dataset (Q^2 > 0.3 GeV^2)
# Epistemology: Data IDs map to specific Jefferson Lab experiments from Ye 2018.
# -----------------------------------------------------------------------------
_raw = np.array([
    # ID 1: Punjabi 2005 (GEp-I / Hall A)
    [0.49, 0.979, 0.016, 0.006, 1], [0.79, 0.951, 0.012, 0.010, 1], 
    [1.18, 0.883, 0.013, 0.018, 1], [1.48, 0.798, 0.029, 0.026, 1], 
    [1.77, 0.789, 0.024, 0.035, 1], [1.88, 0.777, 0.024, 0.033, 1],
    [2.13, 0.747, 0.032, 0.034, 1], [2.47, 0.703, 0.023, 0.033, 1], 
    [2.97, 0.615, 0.029, 0.021, 1], [3.47, 0.606, 0.042, 0.014, 1], 
    # ID 2: Gayou 2001 (Early Hall A)
    [0.32, 0.930, 0.067, 0.007, 2], [0.35, 0.910, 0.061, 0.004, 2],
    [0.39, 0.961, 0.033, 0.005, 2], [0.46, 0.952, 0.034, 0.006, 2], 
    [0.57, 0.959, 0.039, 0.007, 2], [0.76, 0.966, 0.033, 0.012, 2], 
    [0.86, 0.865, 0.029, 0.015, 2], [0.88, 0.923, 0.086, 0.013, 2],
    [1.02, 0.900, 0.038, 0.022, 2], [1.12, 0.825, 0.027, 0.020, 2], 
    [1.18, 0.851, 0.050, 0.023, 2], [1.42, 0.733, 0.058, 0.029, 2], 
    [1.76, 0.816, 0.115, 0.069, 2], 
    # ID 3: Puckett 2012 (GEp-II / Hall A)
    [3.50, 0.571, 0.072, 0.007, 3],
    [3.98, 0.517, 0.055, 0.009, 3], [4.76, 0.450, 0.052, 0.012, 3], 
    [5.56, 0.354, 0.085, 0.019, 3], 
    # ID 4: Strauch 2003 (Hall A)
    [0.515, 0.966, 0.031, 0.012, 4], [1.020, 0.878, 0.021, 0.008, 4], 
    [1.625, 0.765, 0.019, 0.017, 4],
    # ID 8: Ron 2011 (Hall A)
    [0.308, 0.9320, 0.0123, 0.0119, 8], [0.346, 0.9318, 0.0098, 0.0108, 8],
    [0.400, 0.9172, 0.0109, 0.0105, 8], [0.474, 0.9225, 0.0160, 0.0127, 8],
    # ID 9: Jones 2006 (Hall C - RSS)
    [1.51, 0.884, 0.027, 0.029, 9], 
    # ID 10: MacLachlan 2006 (Hall A)
    [1.130, 0.878, 0.064, 0.012, 10],
    # ID 11: Zhan 2011 (Hall A)
    [0.346, 0.9433, 0.0088, 0.0093, 11], [0.402, 0.9318, 0.0066, 0.0076, 11],
    [0.449, 0.9314, 0.0060, 0.0073, 11], [0.494, 0.9286, 0.0054, 0.0076, 11],
    [0.547, 0.9274, 0.0055, 0.0071, 11], [0.599, 0.9084, 0.0053, 0.0104, 11],
    [0.695, 0.9122, 0.0045, 0.0107, 11],
    # ID 12: Paolone 2010 (Hall A)
    [0.80, 0.901, 0.007, 0.010, 12], [1.30, 0.897, 0.008, 0.019, 12],
    # ID 13: Puckett 2017 (GEp-III / Hall C)
    [5.17, 0.448, 0.060, 0.006, 13], [6.70, 0.348, 0.105, 0.010, 13], 
    [8.49, 0.145, 0.175, 0.024, 13],
    # ID 14: Puckett 2017 (GEp-2gamma / Hall C)
    [2.491, 0.6953, 0.0091, 0.0079, 14], [2.477, 0.6809, 0.0070, 0.0040, 14], 
    [2.449, 0.6915, 0.0059, 0.0039, 14]
])
Q2, Rp, Err = _raw[:,0], _raw[:,1], np.hypot(_raw[:,2], _raw[:,3])

# Isolate the Core JLab GEp Campaign (GEp-I, II, III, 2gamma)
# This excludes peripheral/ultra-low-Q2 experiments to strictly probe the topological core
mask_gep = np.isin(_raw[:, 4], [1, 2, 3, 13, 14])

# 2. Physical Constants (from PDG)
HBARC = 0.197327   # GeV fm
M_RHO = 0.775      # Vector meson mass scale (SD bulk)
M_A1  = 1.209      # Axial-Vector mass scale (ASD defect pole)
R_MAG = 0.8510     # Standard magnetic radius baseline (fm)

# 3. CGD 1-Parameter Topological Model (Fixed Mesons)
def cgd_ratio_fit(q2, r_core):
    dipole = lambda q, r: (1.0 + q / (12.0 / (r / HBARC)**2))**-2
    k_theory = (M_RHO / M_A1)**2
    lam2_theory = M_A1**2 - M_RHO**2
    
    gyral_shape = np.log(1.0 + q2 / lam2_theory) * (q2 / (q2 + M_A1**2))
    
    ge = dipole(q2, r_core) * (1.0 - k_theory * gyral_shape)
    gm = dipole(q2, R_MAG)
    return ge / gm

# 4. CGD 3-Parameter Topological Model (Free Mesons)
def cgd_3param_fit(q2, r_core, m_rho, m_a1):
    dipole = lambda q, r: (1.0 + q / (12.0 / (r / HBARC)**2))**-2
    k_theory = (m_rho / m_a1)**2
    lam2_theory = m_a1**2 - m_rho**2
    
    gyral_shape = np.log(1.0 + q2 / lam2_theory) * (q2 / (q2 + m_a1**2))
    
    ge = dipole(q2, r_core) * (1.0 - k_theory * gyral_shape)
    gm = dipole(q2, R_MAG)
    return ge / gm

# 5. Ye 2018 Empirical Fit Baseline (13-Parameter z-expansion spline)
def ye_ratio(q2):
    C_E = [0.239163, -1.109858, 1.444380, 0.479569, -2.286894, 1.126632, 
           1.250619, -3.631020, 4.082217, 0.504097, -5.085120, 3.967742, -0.981529]
    C_M = [0.264142, -1.095306, 1.218553, 0.661136, -1.405678, -1.356418, 
           1.447029, 4.235669, -5.334045, -2.916300, 8.707403, -5.706999, 1.280814]
    z = (np.sqrt(0.07792 + q2) - np.sqrt(0.07792 + 0.7)) / \
        (np.sqrt(0.07792 + q2) + np.sqrt(0.07792 + 0.7))
    return sum(c*(z**i) for i,c in enumerate(C_E)) / sum(c*(z**i) for i,c in enumerate(C_M))

# 6. Execution & Extraction
if __name__ == "__main__":
    
    q, r, e = Q2[mask_gep], Rp[mask_gep], Err[mask_gep]
    n_pts = len(q)
    
    # 1-Parameter fit for the GEp Campaign subset
    popt_1, _ = curve_fit(cgd_ratio_fit, q, r, p0=[0.88], sigma=e, absolute_sigma=True)
    extracted_r_core = popt_1[0]
    
    # 3-Parameter fit (Bounding m_rho and m_a1 away from each other to prevent negative lam2_theory)
    popt_3, _ = curve_fit(cgd_3param_fit, q, r, p0=[0.88, 0.775, 1.209], 
                          bounds=([0.6, 0.4, 1.05], [1.2, 1.0, 2.5]), 
                          sigma=e, absolute_sigma=True)
    r_3, rho_3, a1_3 = popt_3
    
    # Calculate statistics
    p_cgd = np.array([cgd_ratio_fit(x, extracted_r_core) for x in q])
    p_cgd_3 = np.array([cgd_3param_fit(x, r_3, rho_3, a1_3) for x in q])
    p_ye = np.array([ye_ratio(x) for x in q])
    
    chi2_cgd = np.sum(((r - p_cgd)/e)**2)
    chi2_cgd_3 = np.sum(((r - p_cgd_3)/e)**2)
    chi2_ye = np.sum(((r - p_ye)/e)**2)
    
    print("--- CORE JLAB GEp CAMPAIGN ANALYSIS ---")
    print(f"Datasets Included: GEp-I, GEp-II, GEp-III, GEp-2gamma")
    print(f"Total Data Points (N): {n_pts}")
    
    print(f"\nCGD Extracted Parameters (3-param free float):")
    print(f"  m_rho = {rho_3:.4f} GeV (PDG Truth: {M_RHO} GeV)")
    print(f"  m_a1  = {a1_3:.4f} GeV (PDG Truth: {M_A1} GeV)\n")
    
    print(f"{'Model':<30} | {'Params':<6} | {'R_p [fm]':<10} | {'Total χ²':<10}")
    print("-" * 65)
    print(f"{'CGD Topology (Fixed Mesons)':<30} | {1:<6} | {extracted_r_core:<10.4f} | {chi2_cgd:<10.1f}")
    print(f"{'CGD Topology (Free Mesons)':<30} | {3:<6} | {r_3:<10.4f} | {chi2_cgd_3:<10.1f}")
    print(f"{'Ye 2018 Global':<30} | {13:<6} | {'0.879*':<10} | {chi2_ye:<10.1f}")

    # LaTeX Table Output
    print("\n% ==========================================")
    print("% LaTeX Table Output for paper inclusion:")
    print("% ==========================================\n")
    print(r"\begin{table}[h]")
    print(r"\centering")
    print(r"\begin{tabular}{lcccc}")
    print(r"\toprule")
    print(r"\textbf{Model} & \textbf{Parameters} & \textbf{Extracted $R_p$ [fm]} & \textbf{Total $\chi^2$} \\")
    print(r"\midrule")
    print(rf"CGD Topology (Fixed Mesons) & 1 & {extracted_r_core:.4f} & {chi2_cgd:.1f} \\")
    print(rf"CGD Topology (Free Mesons) & 3 & {r_3:.4f} & {chi2_cgd_3:.1f} \\")
    print(rf"Ye 2018 Global & 13 & 0.879* & {chi2_ye:.1f} \\")
    print(r"\bottomrule")
    print(r"\end{tabular}")
    print(r"\caption{\todo{caption}}")
    print(r"\label{tab:proton_radius_fits}")
    print(r"\end{table}")
