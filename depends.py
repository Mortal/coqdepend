import os
import re
import sys
import argparse
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-f', '--filename', default='project.v')
    parser.add_argument('-r', '--root', default='preservation')
    parser.add_argument('-o', '--output', default='deps-preservation.pdf')
    parser.add_argument('-a', '--no-redundant', action='store_false',
                        dest='redundant')
    parser.add_argument('-u', '--unflatten', action='store_true')
    parser.add_argument('-i', '--show-invisible', action='store_true')
    args = parser.parse_args()

    with open(args.filename) as fp:
        s = fp.read()
    toplevel_lemmas_pattern = (
        r'^(?:Lemma|Corollary|Theorem)\s+' +
        r'(?P<name>[a-z_0-9]+)\s*:' +
        r'(?P<body>.*?)' +
        r'(?P<end>Qed|Defined|Admitted|Abort)\.')
    header_pattern = (
        r'^\(\*\* \*\* (?P<header>[^\n]*) \*\)')
    p = '(?:%s|%s)' % (toplevel_lemmas_pattern, header_pattern)
    matches = re.finditer(p, s, re.S | re.M)

    all_nodes = {}
    edge_lists = {}

    section = None
    section_colors = {
        # 'Intro': '',
        # 'Definitions': '',
        'Commutativity results': 'pink',
        'The typing relation': 'blue',
        'Church encodings': 'green',
        'Preservation of types under beta reductions': 'blue',
        'Progress': 'blue',
        'Logical relations': 'green',
    }

    i = 0
    line_number = 1
    prev_start = 0
    for mo in matches:
        line_number += s.count('\n', prev_start, mo.start(0))
        prev_start = mo.start(0)

        matched_lines = mo.group(0).count('\n') + 1

        if mo.group('header') is not None:
            section = mo.group('header')
            continue

        u = mo.group('name')
        node_color = section_colors.get(section)
        i += 1
        node_label = '%d: %s' % (line_number, u)
        all_nodes[u] = {
            'color': node_color,
            'label': node_label,
            'lines': matched_lines,
        }
        edge_lists[u] = set(edge_lists.keys()).intersection(
            m.group(0) for m in re.finditer(r'[a-z_0-9]+', mo.group('body')))

    edge_lists['ROOT'] = set('''
        preservation progress typecheck_sound typecheck_complete
    '''.split())

    edge_lists['CHURCH'] = set('''
        church_pair_tapp_typed fst_app_typed pair_typed
    '''.split())

    edge_lists['LR'] = set('''
        fundamental_property
        normalize_forward
        safe_expressions
        subs_terms_value
        term_normalizes
    '''.split())

    def nodes_from(u):
        if u not in nodes_from.cache:
            neighbors = [nodes_from(v) for v in edge_lists[u]]
            closure = set().union(*neighbors)
            nodes_from.cache[u] = closure.union(edge_lists[u])
        return nodes_from.cache[u]

    nodes_from.cache = {}

    def non_redundant_edges(u):
        e = set(edge_lists[u])
        neighbors = [nodes_from(v) for v in edge_lists[u]]
        closure = set().union(*neighbors)
        removed = closure & e
        if removed:
            print("Implied by transitivity: %s -> %s" %
                  (u, ', '.join(removed)))
        e.difference_update(closure)
        return e

    def subgraph(u):
        return nodes_from(u) | {u}

    def total_lines(u):
        if 'total_lines' not in all_nodes[u]:
            all_nodes[u]['total_lines'] = sum(
                all_nodes[v]['lines'] for v in subgraph(u))
        return all_nodes[u]['total_lines']

    for u in all_nodes:
        all_nodes[u]['label'] = '%s (%s)' % (
            all_nodes[u]['label'], total_lines(u))

    edges = set((u, v) for u, vs in edge_lists.items() for v in vs)
    unused = set(all_nodes).difference(v for u, v in edges)
    sys.stderr.write(''.join('%s\n' % v for v in sorted(unused)))

    if args.root == 'all':
        nodes = set(all_nodes)
    elif args.root.startswith('+'):
        roots = set(all_nodes) - subgraph(args.root[1:])
        subgraphs = [subgraph(r) for r in roots]
        nodes = set().union(*subgraphs)
    else:
        subgraphs = [subgraph(r) for r in args.root.split(',')]
        nodes = set().union(*subgraphs)

    if args.output:
        base, fmt = os.path.splitext(args.output)
        if fmt == '.tex':
            cmdline = ('dot', '-o', base + '.dot')
        else:
            cmdline = ('dot', '-T%s' % fmt[1:], '-o', args.output)
    else:
        cmdline = ('xdot',)

    if args.unflatten:
        p1 = subprocess.Popen(
            ('unflatten', '-l', '100'), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, universal_newlines=True)
        p = subprocess.Popen(
            cmdline, stdin=p1.stdout, universal_newlines=True)
        fp = p1.stdin
    else:
        p = subprocess.Popen(
            cmdline, stdin=subprocess.PIPE, universal_newlines=True)
        fp = p.stdin
    print('digraph {', file=fp)
    # print('size=5', file=fp)
    print('margin=0;', file=fp)
    print('node [shape=box fontsize="10" margin="0.055,0.055"];', file=fp)
    print('node [fontname="Serif" height=0];', file=fp)
    # print('ratio="compress";', file=fp)
    # print('rankdir=LR;', file=fp)
    for n in sorted(nodes):
        attrs = {}
        attrs['label'] = '"%s"' % all_nodes[n]['label']
        if n in unused:
            attrs['color'] = 'red'
        else:
            color = all_nodes[n]['color']
            if color:
                attrs['color'] = color

        print('"%s" [%s];' %
              (n, ', '.join('%s=%s' % x for x in attrs.items())),
              file=fp)

    for u in sorted(nodes):
        if args.redundant:
            e = edge_lists[u]
        else:
            e = non_redundant_edges(u)
        for v in sorted(e):
            print('"%s" -> "%s";' % (u, v), file=fp)
    invis = [l.split() for l in '''
        lookup_map typed_type_shift_cut subs_comm_0
        subs_type_shift_le_env subs_comm_0
        lookup_app_lt lookup_app_gt subs_comm_0
        subs_multi_shift_comm_var subs_type_shift_ge_var shift_env_comm
        multi_shift_type_cut_twice_eq multi_shift_type_cut_twice_helper
        shift_type_cut_var shift_comm_strict
        pair_typed subs_shift_0_env
        church_pair_tapp_typed fst_app_typed
        func_invert_tapp func_invert_tlam typecheck_complete preservation
        func_invert_lam func_invert_app
        eq_type_dec church_pair_tapp_typed
        typecheck_complete progress
    '''.strip().splitlines()]
    for edges in invis:
        e = []
        for u in edges:
            if u not in edge_lists:
                raise ValueError(u)
            elif u in nodes:
                e.append(u)
        if len(e) > 1:
            print('%s [style=%s];' %
                  (' -> '.join('"%s"' % v for v in e),
                   'dashed' if args.show_invisible else 'invis'),
                  file=fp)
    print('}', file=fp)
    fp.close()
    if args.unflatten:
        p1.wait()
    p.wait()

    if fmt == '.tex':
        with open(args.output, 'w') as fp:
            subprocess.check_call(
                ('dot2tex', base + '.dot'),
                stdout=fp,
                universal_newlines=True)


if __name__ == "__main__":
    main()
