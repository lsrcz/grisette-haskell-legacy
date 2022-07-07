#!/bin/env python3

import subprocess
import csv
import math
import os
import io
import argparse


projectname = {'nanoscala': 'NanoScala',
               'letpoly': 'LetPoly',
               'regex': 'Regex',
               'ferrite': 'Ferrite',
               'fluidics': 'Fluidics',
               'ifcl': 'IFCL',
               'cosette': 'Cosette',
               'cosette-1': 'Cosette-1',
               'regex': 'RegexFree',
               'regex-delim': 'RegexCont'
               }


def print_raw_data(org, meg):
    print('--------------------------------- Raw data ORG ---------------------------------')
    print(org)
    print('--------------------------------- Raw data MEG ---------------------------------')
    print(meg)


def parse_csv(data, grisette):
    ret = {}
    for row in csv.DictReader(data):
        for k in row:
            if k != 'subject':
                row[k] = float(row[k])
                if not grisette or k == 'term':
                    row[k] /= 1000
        ret[row['subject']] = row
    return ret


def format_number(number):
    if number >= 10:
        return '{:d}'.format(round(number))
    if number > 1:
        return '{:.1f}'.format(number)
    elif number < 0.01:
        return '{:.1g}'.format(number)[1:]
    else:
        return '{:.2g}'.format(number)[1:]


class Tabular:
    def __init__(self, pre, epi, col):
        self.pre = pre
        self.epi = epi
        self.col = col
        self.tab = []

    def add_row(self, row):
        assert(len(row) == self.col)
        self.tab.append(row)

    def add_hline(self):
        self.tab.append(r'  \hline')

    def col_width(self):
        ret = []
        for i in range(self.col):
            ret.append(0)
            for l in self.tab:
                if isinstance(l, list):
                    w1 = len(l[i])
                    ret[-1] = max(w1, ret[-1])
            if ret[-1] != 0:
                ret[-1] += 1
        return ret

    def normalize(self):
        width = self.col_width()
        for row in self.tab:
            if isinstance(row, list):
                for i in range(self.col):
                    row[i] = row[i].ljust(width[i])

    def __str__(self):
        lst = []
        lst += self.pre
        lst += list(map(lambda x: '&'.join(x) +
                    r"\\" if isinstance(x, list) else x, self.tab))
        lst += self.epi
        return '\n'.join(lst)


def basic_comparison(org, meg, r3, r4):
    pre = [r'\begin{tabular}{lrrrrrrrrrrrrrrrrrrrrr}',
           r'  \hline',
           r'  \multirow{2}{*}{Benchmark}&\multicolumn{5}{c}{\textsc{Grisette}}&&\multicolumn{5}{c}{\textsc{Grisette} (MEG)}' +
           r'&&\multicolumn{4}{c}{\textsc{Rosette} 3}&&\multicolumn{4}{c}{\textsc{Rosette} 4}\\',
           r'  \cline{2-6}\cline{8-12}\cline{14-17}\cline{19-22}',
           ]
    epi = [r'  \hline', r'\end{tabular}']

    tabular = Tabular(pre, epi, 22)
    tabular.add_row(['', 'T', 'E', 'L', 'S', 'Tm'] *
                    2 + ['', 'T', 'E', 'S', 'Tm'] * 2)
    tabular.add_hline()

    for project in ['ferrite', 'ifcl', 'fluidics', 'cosette', 'nanoscala', 'letpoly', 'cosette-1', 'regex-delim', 'regex']:
        if project == 'cosette-1' or project == 'regex-delim':
            tabular.add_hline()

        new_row = ['  \\textsc{{{}}}'.format(projectname[project])]

        tab_map = {'org': org, 'meg': meg, 'r3': r3, 'r4': r4}
        if project.startswith('regex'):
            tabs = ['org', 'meg']
        else:
            tabs = ['org', 'meg', 'r3', 'r4']

        start = True
        for tabname in tabs:
            if start:
                start = False
            else:
                new_row.append('')
            if tabname in ['org', 'meg']:
                for column in ['total', 'eval', 'lower', 'solv', 'term']:
                    new_row.append(format_number(
                        tab_map[tabname][project][column]))
            else:
                for column in ['total', 'eval', 'solv', 'term']:
                    new_row.append(format_number(
                        tab_map[tabname][project][column]))
        if project.startswith('regex'):
            new_row += [''] * 10

        tabular.add_row(new_row)
    tabular.normalize()
    return tabular


def error_encoding(org):
    pre = [r'\begin{tabular}{lrrrrrrrrrrr}',
           r'  \hline',
           r'  \multirow{2}{*}{Benchmark}&\multicolumn{5}{c}{\textsc{Grisette}}&&\multicolumn{5}{c}{\textsc{Grisette} (CBMC error encoding)}\\'
           r'  \cline{2-6}\cline{8-12}',
           ]
    epi = [r'  \hline', r'\end{tabular}']

    tabular = Tabular(pre, epi, 12)
    tabular.add_row(['', 'Total', 'Eval', 'Lower', 'Solve', 'Term'] * 2)
    tabular.add_hline()

    for project in ['ifcl', 'nanoscala', 'letpoly']:
        new_row = ['  \\textsc{{{}}}'.format(projectname[project])]

        start = True
        for suffix in ['', '-cbmc']:
            if start:
                start = False
            else:
                new_row.append('')
            for column in ['total', 'eval', 'lower', 'solv', 'term']:
                new_row.append(format_number(
                    org[project + suffix][column]))
        tabular.add_row(new_row)
    tabular.normalize()
    return tabular


def geomean(xs):
    return math.exp(math.fsum(math.log(x) for x in xs) / len(xs))


def summary(org, meg, r3, r4):
    pre = [r'\begin{tabular}{lrrrrrrrrrrrrrrr}',
           r'  \hline'
           r'  \multirow{2}{*}{Version}&\multicolumn{3}{c}{Total time}&&\multicolumn{3}{c}{Eval time}' +
           r'&&\multicolumn{3}{c}{Solve time}&&\multicolumn{3}{c}{Term count}\\',
           r'  \cline{2-4}\cline{6-8}\cline{10-12}\cline{14-16}',
           ]
    epi = [r'  \hline', r'\end{tabular}']

    tot_l = {'org': [], 'meg': [], 'r3': [], 'r4': []}
    eval_l = {'org': [], 'meg': [], 'r3': [], 'r4': []}
    solv_l = {'org': [], 'meg': [], 'r3': [], 'r4': []}
    term_l = {'org': [], 'meg': [], 'r3': [], 'r4': []}
    metrics = {'total': tot_l, 'eval': eval_l, 'solv': solv_l, 'term': term_l}
    tbls = {'org': org, 'meg': meg, 'r3': r3, 'r4': r4}
    for project in ['ferrite', 'ifcl', 'fluidics', 'cosette', 'nanoscala', 'letpoly', 'cosette-1']:
        for m in metrics:
            for t in tbls:
                metrics[m][t].append(tbls[t][project][m])

    system_name = {
        'meg': r'\textsc{Grisette} (MEG)', 'r3': r'\textsc{Rosette} 3', 'r4': r'\textsc{Rosette} 4'}
    tabular = Tabular(pre, epi, 16)
    tabular.add_row(['', 'best', 'worst', 'mean'] * 4)
    tabular.add_hline()
    for t in ['meg', 'r3', 'r4']:
        row = [system_name[t]]
        for m in ['total', 'eval', 'solv', 'term']:
            if m != 'term':
                l = list(map(lambda p: p[1] / p[0],
                         zip(metrics[m]['org'], metrics[m][t])))
                best = max(*l)
                worst = min(*l)
                mean = geomean(l)
                row += ['{:.1f}x'.format(best), '{:.1f}x'.format(worst),
                        '{:.1f}x'.format(mean), '']
            else:
                l = list(map(lambda p: p[0] / p[1],
                         zip(metrics[m]['org'], metrics[m][t])))
                best = min(*l)
                worst = max(*l)
                mean = geomean(l)
                row += ['{:.1f}\\%'.format(best * 100), '{:.1f}\\%'.format(
                    worst * 100), '{:.1f}\\%'.format(mean * 100)]
        tabular.add_row(row)
    tabular.normalize()
    return tabular


def memo_summary(org):
    pre = [r'\begin{tabular}{lrrrrrrrrrrrr}',
           r'  \hline',
           r'  \multirow{2}{*}{Benchmark}&\multicolumn{4}{c}{no memoization}&&' +
           r'\multicolumn{4}{c}{with memoization}&&\multicolumn{2}{c}{speedup ratio}\\',
           r'  \cline{2-5}\cline{7-10}\cline{12-13}']
    epi = [r'  \hline', r'\end{tabular}']
    tabular = Tabular(pre, epi, 13)
    tabular.add_row(['', 'Total', 'Eval', 'Lower', 'Solv']
                    * 2 + ['', 'Total', 'Eval'])
    tabular.add_hline()

    for project in ['nanoscala', 'letpoly', 'regex-delim', 'regex']:
        row = ['  \\textsc{{{}}}'.format(projectname[project])]
        for m in ['-nomemo', '']:
            for t in ['total', 'eval', 'lower', 'solv']:
                row.append(format_number(org[project + m][t]))
            row.append('')
        row.append(format_number(
            org[project + '-nomemo']['total'] / org[project]['total']) + 'x')
        row.append(format_number(
            org[project + '-nomemo']['eval'] / org[project]['eval']) + 'x')
        tabular.add_row(row)
    tabular.normalize()
    return tabular


def main():
    parser = argparse.ArgumentParser(
        description='Run benchmarks and draw graphs for Grisette')
    parser.add_argument('--rerun', action='store_true',
                        help='rerun benchmarks')
    parser.add_argument('--r3', type=str, required=True, help='Rosette 3 CSV')
    parser.add_argument('--r4', type=str, required=True, help='Rosette 4 CSV')
    parser.add_argument('--skip', type=int, default=0,
                        help='Skip first N executions')
    parser.add_argument('--ntimes', type=int, default=1,
                        help='Skip first N executions')
    args = parser.parse_args()
    print(args)

    dirname, _ = os.path.split(os.path.abspath(__file__))
    orgCsvPath = os.path.join(dirname, 'org.csv')
    megCsvPath = os.path.join(dirname, 'meg.csv')
    if not args.rerun and os.path.exists(orgCsvPath) and os.path.exists(megCsvPath):
        with open(orgCsvPath, 'r') as csvfile:
            org = csvfile.read()
        with open(megCsvPath, 'r') as csvfile:
            meg = csvfile.read()
    else:
        orgProc = subprocess.Popen(" ".join([os.path.join(
            dirname, 'runallbench.sh'), "--skip", str(args.skip), "--ntimes", str(args.ntimes), "all"]), shell=True, stdout=subprocess.PIPE)
        megProc = subprocess.Popen(" ".join([os.path.join(
            dirname, 'runallbench.sh'), "--skip", str(args.skip), "--ntimes", str(args.ntimes), "-u", "all"]), shell=True, stdout=subprocess.PIPE)
        org = orgProc.stdout.read().decode('utf-8')
        with open(orgCsvPath, 'w') as f:
            f.write(org)

        meg = megProc.stdout.read().decode('utf-8')
        with open(megCsvPath, 'w') as f:
            f.write(meg)

    with open(args.r3, 'r') as csvfile:
        r3 = csvfile.read()
    with open(args.r4, 'r') as csvfile:
        r4 = csvfile.read()

    orgDict = parse_csv(io.StringIO(org), True)
    megDict = parse_csv(io.StringIO(meg), True)
    r3Dict = parse_csv(io.StringIO(r3), False)
    r4Dict = parse_csv(io.StringIO(r4), False)

    print(basic_comparison(orgDict, megDict, r3Dict, r4Dict))
    print(summary(orgDict, megDict, r3Dict, r4Dict))
    print(error_encoding(orgDict))
    print(memo_summary(orgDict))

    # printBasicComparison(orgDict, megDict)


if __name__ == '__main__':
    main()
