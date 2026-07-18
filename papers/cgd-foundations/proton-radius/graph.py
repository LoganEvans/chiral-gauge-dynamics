# FILENAME: paper/proton-radius/graph.py

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from pathlib import Path
import sys

from analysis import Q2, Rp, Err, mask_gep, cgd_ratio_fit, cgd_3param_fit, ye_ratio

def find_repo_root():
    """Walks up the directory tree to find the repository root."""
    current = Path(__file__).resolve().parent
    for _ in range(10):  # Safety limit
        if (current / ".git").exists() or (current / "flake.lock").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find repository root (missing .git/ or flake.lock).")

# 1. Filter Data for the Core JLab GEp Campaign
q = Q2[mask_gep]
r = Rp[mask_gep]
e = Err[mask_gep]

# 2. Perform the Fits
popt_1, _ = curve_fit(cgd_ratio_fit, q, r, p0=[0.88], sigma=e, absolute_sigma=True)
extracted_r_core = popt_1[0]

popt_3, _ = curve_fit(cgd_3param_fit, q, r, p0=[0.88, 0.775, 1.209], 
                      bounds=([0.6, 0.4, 1.05], [1.2, 1.0, 2.5]), 
                      sigma=e, absolute_sigma=True)
r_3, rho_3, a1_3 = popt_3

# 3. Generate smooth lines for plotting
Q2_plot = np.geomspace(0.1, 10.0, 400)
ye_line = [ye_ratio(x) for x in Q2_plot]
cgd_line = [cgd_ratio_fit(x, extracted_r_core) for x in Q2_plot]
cgd_3_line = [cgd_3param_fit(x, r_3, rho_3, a1_3) for x in Q2_plot]

# 4. Figure Setup
plt.figure(figsize=(8, 5))

# Plot the filtered Core JLab GEp Campaign data
plt.errorbar(q, r, yerr=e, fmt='o', color='black', markersize=4.5, 
             label=r'JLab GEp Campaign (Hall C)', zorder=5)

# Plot Ye 2018 13-Parameter Baseline
plt.plot(Q2_plot, ye_line, '--', color='red', linewidth=2, 
         label='Ye 2018 Global Fit (13-Param)', zorder=4)

# Plot CGD 3-Parameter Topological Shape
plt.plot(Q2_plot, cgd_3_line, ':', color='purple', linewidth=2.5, 
         label=f'CGD Topology (3-Param Free Float)', zorder=5.5)

# Plot CGD 1-Parameter Topological Shape
plt.plot(Q2_plot, cgd_line, '-', color='#4477AA', linewidth=2.5, 
         label=f'CGD Topology (1-Param: $r_p$ = {extracted_r_core:.4f} fm)', zorder=6)

# 5. Axes and Formatting
plt.xscale('log')
plt.xlim(0.25, 10.0)
plt.ylim(0.0, 1.1)
plt.xlabel(r'$Q^2$ [GeV$^2$]', fontsize=12)
plt.ylabel(r'$R_p = \mu_p G_E / G_M$', fontsize=12)
plt.title('Proton Core Form Factor', fontsize=13)
plt.legend(loc='lower left', fontsize=10, frameon=True, framealpha=0.9)
plt.grid(True, which="both", ls="--", alpha=0.2)
plt.tight_layout()

# 6. Save Output
repo_root = find_repo_root()
output_path = repo_root / "papers" / "cgd-foundations" / "proton-radius" / "jlab-hall-C-polarization-transfer.pdf"

# Ensure target directory exists
output_path.parent.mkdir(parents=True, exist_ok=True)

plt.savefig(output_path, format='pdf', bbox_inches='tight')
print(f"Successfully generated and saved plot to {output_path}")
