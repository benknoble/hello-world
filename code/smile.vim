let sm = execute('smile')->split('\n')
let sm_t = timer_start(30 * 60 * 1000, {-> popup_atcursor(g:sm, #{border: []})}, #{repeat: -1})
