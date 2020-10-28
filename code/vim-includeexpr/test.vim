augroup Mine
  autocmd!
  autocmd BufWinEnter myfile call TestMyFile()
augroup END

function TestMyFile() abort
  let &l:include='^\s*include'
  setlocal includeexpr=TestInclude(v:fname)
  setlocal suffixesadd=dummy
endfunction

function TestInclude(fname) abort
  return [a:fname..'/init.dummy', a:fname..'.'..split(&l:suffixesadd, ',')[0]]
  " return a:fname..'.'..split(&l:suffixesadd, ',')[0]
endfunction
