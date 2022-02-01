from popper.util import Settings, parse_settings
from popper.dcc import dcc

if __name__ == '__main__':
    settings = parse_settings()
    if settings.hspace:
        show_hspace(settings)
    else:
        _prog, stats = dcc(settings)
        if settings.stats:
            stats.show()

            # if best_prog:
    #     best_prog_errors = calc_score(tester, best_prog)
    #     dbg(f'best_prog size:{best_prog_size} errors:{best_prog_errors}')
    #     for x in best_prog:
    #         dbg('\t'+ x.to_code())
    #     print('STATS.OLD_RULES', stats.old_rules)
    #     print('STATS.CRAP_COUNT', stats.crap_count)
    #     print('STATS.REDUNDANT_LITERAL', stats.redundant_literal)
    #     print('STATS.REDUNDANT_CLAUSE', stats.redundant_clause)
    #     stats.show()
    #     return