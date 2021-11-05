if exists('g:loaded_buffy')
  finish
endif
let g:loaded_buffy = 1

call prop_type_add('buffy', #{highlight: 'Special'})

function Buffy() abort
  const scriptfile = tempname()
  execute 'split' scriptfile
  setlocal nobuflisted bufhidden=wipe
  setfiletype buffy.vim
  command! -buffer Slay silent write | source % | close

  const buffers = getbufinfo(#{buflisted: v:true})
        \ ->filter({_, v -> !empty(v.name)})
        \ ->map({_, v -> '" bdelete ' .. v.name})
  const message = [
        \ '" Buffy the buffer slayer',
        \ '" Uncomment the buffers you want to delete',
        \ '" Then run :Slay to delete the buffers and close this window',
        \ ]
  silent put =buffers
  silent 0put =message
  silent write

  call prop_add(1, 1, #{end_lnum: 2, type: 'buffy'})
  call prop_add(2, 1, #{end_lnum: 3, type: 'buffy'})
  call prop_add(3, 1, #{end_lnum: 4, type: 'buffy'})
endfunction

command Buffy call Buffy()
