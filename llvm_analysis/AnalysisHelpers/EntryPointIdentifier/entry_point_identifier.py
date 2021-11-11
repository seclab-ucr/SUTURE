import sys, os

def _process_entry_out(output_file, target_bc_file, analysis_funcs):
    out_cache = []
    out_cache_cand = {}
    fp = open(output_file, 'r')
    all_lines = fp.readlines()
    for curr_li in all_lines:
        curr_li = curr_li.strip()
        if curr_li:
            tks = curr_li.split(':')
            if tks[0].endswith('_CAND'):
                if not tks[1] in out_cache_cand:
                    out_cache_cand[tks[1]] = (tks[0], tks[2])
            elif not tks[1] in out_cache:
                out_cache.append(tks[1])
                analysis_funcs.append('#' + tks[2] + '\n' + tks[1] + ' ' + tks[0])
    for k in out_cache_cand:
        if not k in out_cache:
            analysis_funcs.append('#' + out_cache_cand[k][1] + '\n' + k + ' ' + out_cache_cand[k][0])
    fp.close()

entry_point_bin = './entry_point_handler'

def generate_entry_points(bc, entry_point_file=None):
    out_analysis_funcs = []
    if not os.path.exists(bc):
        print('The specified bc file does not exist.')
        return False
    entry_point_out = bc + '.all_entries'
    if entry_point_file and os.path.exists(entry_point_file):
        os.system(entry_point_bin + ' ' + bc + ' ' + entry_point_out + ' ' + entry_point_file)
    else:
        os.system(entry_point_bin + ' ' + bc + ' ' + entry_point_out)
    assert(os.path.exists(entry_point_out))
    _process_entry_out(entry_point_out, bc, out_analysis_funcs)
    fp = open(entry_point_out, "w")
    for curr_en in sorted(out_analysis_funcs):
        fp.write(curr_en + "\n")
    fp.close()
    return True

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: entry_identifier.py path/to/bitcode')
    else:
        generate_entry_points(sys.argv[1])
