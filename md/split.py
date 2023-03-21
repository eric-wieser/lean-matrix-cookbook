import re

with open('md/main.md') as f:
    main = f.read()

parts = iter(re.split(r'(?=\\section\{)', main))
assert next(parts).strip() == ''

eq_starts = {
    0: 1,
    1: 1,
    2: 32,
    3: 145,
    4: 225,
    5: 260,
    6: 303,
    7: 335,
    8: 346,
    9: 397,
    10: 487,
    11: 551,
}

def fix_headers(s):
    s = re.sub(r'\\section\{(.*)\}', r'# \1', s)
    s = re.sub(r'\\subsection\{(.*)\}', r'## \1', s)
    s = re.sub(r'\\subsubsection\{(.*)\}', r'### \1', s)
    return s

def fix_all(s):
    s = fix_headers(s)
    s = re.sub(r'\n\n\$\$', r'\n-/\n\n/- $$', s)
    s = re.sub(r'\$\$\n\n', r'$$ -/\n\n/-!\n', s)
    return '/-!' + s + '-/'


def headers_only(s):
    s = fix_headers(s)
    return  '\n\n'.join([
        f'/-! {h} -/' for h in re.findall(r'#+ .*(?=\n)', s)
    ])

for i, p in enumerate(parts, start=0):
    header = re.search(r'\\section\{([^\}]*)\}', p)
    header_slug = str(i) + '_' + header.group(1).lower().replace(' ', '_')
    p = fix_headers(p)
    with open('md/' + header_slug + '.lean', 'w') as f:
        f.write(headers_only(p))
        for eq_i in range(eq_starts[i], eq_starts[i+1]):
            print(f'lemma eq_{eq_i} : sorry := sorry', file=f)
