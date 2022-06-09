#!/usr/bin/env python3

import matplotlib.pyplot as plt
import matplotlib.cbook as cbook
import matplotlib as lib
import numpy as np
from matplotlib.backends.backend_pdf import PdfPages

def plot_sim():
    data = np.genfromtxt('sim-cpp.csv', dtype=None, delimiter=',', names=True)

    fig = plt.figure()
    plt.rcParams.update({'font.size': 11})

    plt.errorbar(data['name'], data['mean'], data['stddev'],
                 linestyle='None', marker='o',
                 label='Random simulation',
                 ecolor='red',
                 color='red',
                 markersize=3,
                 capsize=3)
    plt.xlabel('Simulation for L steps, A addresses, V values')
    plt.ylabel('Time, seconds')
    plt.xticks(rotation=35)
    #plt.semilogy()
    plt.ylim([-30, 400])
    plt.grid(True, alpha=.2)
    plt.legend(loc=0)
    plt.tight_layout()
    with PdfPages('sim-cpp.pdf') as pdf:
        pdf.savefig(fig)

    plt.clf()

def plot_apa_sim():
    data = np.genfromtxt('apa-simulate.csv',
                         dtype=None, delimiter=',', names=True)

    fig = plt.figure()
    plt.rcParams.update({'font.size': 11})

    plt.errorbar(data['name'], data['mean'], data['stddev'],
                 linestyle='None', marker='o',
                 label='Apalache simulate',
                 ecolor='blue',
                 color='blue',
                 markersize=3,
                 capsize=3)
    plt.xlabel('Symbolic simulation for L steps, A addresses, V values')
    plt.ylabel('Time, seconds')
    plt.xticks(rotation=30)
    #plt.semilogy()
    plt.ylim([-30, 400])
    plt.grid(True, alpha=.2)
    plt.legend(loc=0)
    plt.tight_layout()
    with PdfPages('apa-simulate.pdf') as pdf:
        pdf.savefig(fig)

    plt.clf()

def plot_apa_check():
    data = np.genfromtxt('apa-check.csv',
                         dtype=None, delimiter=',', names=True)

    fig = plt.figure()
    plt.rcParams.update({'font.size': 11})

    plt.errorbar(data['name'], data['mean'], data['stddev'],
                 linestyle='None', marker='o',
                 label='Apalache check',
                 color='green',
                 ecolor='green',
                 markersize=3,
                 capsize=3)
    plt.xlabel('Bounded MC for L steps, A addresses, V values')
    plt.ylabel('Time, seconds')
    plt.xticks(rotation=40)
    #plt.semilogy()
    plt.ylim([-30, 400])
    plt.grid(True, alpha=.2)
    plt.legend(loc=0)
    plt.tight_layout()
    with PdfPages('apa-check.pdf') as pdf:
        pdf.savefig(fig)

    plt.clf()

if __name__ == "__main__":
    plt.rc('figure', figsize=[7,6])
    plot_sim()
    plot_apa_sim()
    plot_apa_check()
