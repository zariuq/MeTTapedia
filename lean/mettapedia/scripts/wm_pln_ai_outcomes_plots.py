#!/usr/bin/env python3
"""
AI Outcomes assumption ladder figure for the WM-PLN book.
Reads the assumption ladder CSV and produces a 2×3 panel figure
showing interval widening at A2 (reliability filtering).
"""

import csv
import os
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(SCRIPT_DIR, '..', 'results', 'ai_outcomes')
OUT_DIR = os.path.join(SCRIPT_DIR, '..', 'results', 'figures')

# Read the assumption ladder CSV
rows = []
with open(os.path.join(DATA_DIR, 'ai_outcomes_assumption_ladder.csv')) as f:
    reader = csv.DictReader(f)
    for row in reader:
        rows.append(row)

# Parse into structured data
lenses = ['beneficial_pluralistic_transition', 'mixed_reversible_world',
          'authoritarian_lock_in', 'catastrophic_disempowerment',
          'extinction', 'p_doom']
lens_labels = ['Beneficial\nTransition', 'Mixed\nWorld',
               'Authoritarian\nLock-in', 'Catastrophic\nDisempowerment',
               'Extinction', 'p_doom\n(Fréchet)']
assumption_levels = ['A0_evidence_only', 'A1_weak_direct_numeric_hull',
                     'A2_reliability_filtered_numeric_hull',
                     'A3_monotone_regime_ordering']
level_labels = ['A0\n(evidence\nonly)', 'A1\n(weak\nnumeric)', 'A2\n(reliability\nfiltered)', 'A3\n(regime\nordering)']

# Direct-target row counts per lens
row_counts = {
    'beneficial_pluralistic_transition': 40,
    'mixed_reversible_world': 627,
    'authoritarian_lock_in': 10,
    'catastrophic_disempowerment': 8,
    'extinction': 12,
    'p_doom': 20,
}

data = {}
for row in rows:
    key = (row['lens'], row['assumption_level'])
    data[key] = (float(row['interval_low']), float(row['interval_high']))

# Create figure
fig, axes = plt.subplots(2, 3, figsize=(14, 9), sharey=True)
axes = axes.flatten()

bar_width = 0.5
colors = {
    'A0_evidence_only': '#cccccc',                       # gray: full width
    'A1_weak_direct_numeric_hull': '#4477aa',            # blue: narrowed
    'A2_reliability_filtered_numeric_hull': '#cc6677',   # red: reopened
    'A3_monotone_regime_ordering': '#cccccc',             # gray: still full width
}

for idx, (lens, label) in enumerate(zip(lenses, lens_labels)):
    ax = axes[idx]
    for j, (alevel, alabel) in enumerate(zip(assumption_levels, level_labels)):
        lo, hi = data.get((lens, alevel), (0, 1))
        color = colors[alevel]
        # Draw interval bar
        ax.bar(j, hi - lo, bottom=lo, width=bar_width, color=color,
               edgecolor='black', linewidth=0.5)
        # Annotate narrowed intervals with values
        if hi - lo < 0.95:
            ax.text(j, (lo + hi) / 2, f'[{lo:.2f},\n{hi:.2f}]',
                    ha='center', va='center', fontsize=8, fontweight='bold')

    ax.set_xticks(range(4))
    ax.set_xticks(range(4))
    ax.set_xticklabels(level_labels, fontsize=8)
    ax.set_ylim(0, 1.05)
    ax.set_title(f'{label}\n(n={row_counts[lens]})', fontsize=11, fontweight='bold')
    if idx % 3 == 0:
        ax.set_ylabel('Probability interval', fontsize=10)

    # Annotate A1→A2 transition
    if lens != 'p_doom':
        ax.annotate('', xy=(2, 0.97), xytext=(1, 0.97),
                    arrowprops=dict(arrowstyle='->', color='#cc6677', lw=1.5))
        ax.text(1.5, 1.01, 'reopens', ha='center', va='bottom',
                fontsize=6, color='#cc6677', fontstyle='italic')

# Legend
legend_elements = [
    mpatches.Patch(facecolor='#cccccc', edgecolor='black', label='Full width [0, 1]'),
    mpatches.Patch(facecolor='#4477aa', edgecolor='black', label='Data-narrowed'),
    mpatches.Patch(facecolor='#cc6677', edgecolor='black', label='Reliability-filtered (reopened)'),
]
fig.legend(handles=legend_elements, loc='lower center', ncol=3,
           fontsize=9, frameon=True, bbox_to_anchor=(0.5, -0.02))

fig.suptitle('Assumption Ladder: AI Outcome Intervals by Evidence Level',
             fontsize=12, fontweight='bold', y=1.02)
plt.tight_layout()

os.makedirs(OUT_DIR, exist_ok=True)
outpath = os.path.join(OUT_DIR, 'ai_outcomes_assumption_ladder.pdf')
fig.savefig(outpath, bbox_inches='tight', dpi=150)
print(f'Saved: {outpath}')

# Also save PNG for preview
fig.savefig(outpath.replace('.pdf', '.png'), bbox_inches='tight', dpi=150)
print(f'Saved: {outpath.replace(".pdf", ".png")}')
