let s:tags = {
      \ "length": 3,
      \ "curidx": 4,
      \ "items": [
      \   {
      \     "bufnr": 37,
      \     "tagname": "gettagstack()@en",
      \     "from": [
      \       37,
      \       1,
      \       1,
      \       0
      \     ],
      \     "matchnr": 1
      \   },
      \   {
      \     "bufnr": 10,
      \     "tagname": "list-index@en",
      \     "from": [
      \       10,
      \       5897,
      \       25,
      \       0
      \     ],
      \     "matchnr": 1
      \   },
      \   {
      \     "bufnr": 10,
      \     "tagname": "tagstack@en",
      \     "from": [
      \       10,
      \       5923,
      \       8,
      \       0
      \     ],
      \     "matchnr": 1
      \   }
      \ ]
      \ }

let s:lines = mapnew(tags.items, funcref('FormatTagItem'))

let s:item_length = max([strlen('Item')] + mapnew(s:lines, {_, v -> strlen(v.item)})) + 1
let s:tag_length = max([strlen('Tag')] + mapnew(s:lines, {_, v -> strlen(v.tag)})) + 1
let s:match_length = max([strlen('Match')] + mapnew(s:lines, {_, v -> strlen(v.match)})) + 1
let s:file_length = max([strlen('File')] + mapnew(s:lines, {_, v -> strlen(v.file)})) + 1

let text = [
      \   'Item' . repeat(' ', s:item_length - strlen('Item')) .
      \   'Tag' . repeat(' ', s:tag_length - strlen('Tag')) .
      \   'Match' . repeat(' ', s:match_length - strlen('Match')) .
      \   'File' . repeat(' ', s:file_length - strlen('File')) .
      \   'Origin']
      \ + mapnew(s:lines, {k, v -> printf('%s%s%s%s%s%s',
      \   (k is# s:tags.curidx - 1) ? '>' : '',
      \   v.item . repeat(' ', s:item_length - strlen(v.item)),
      \   v.tag . repeat(' ', s:tag_length - strlen(v.tag)),
      \   v.match . repeat(' ', s:match_length - strlen(v.match)),
      \   v.file . repeat(' ', s:file_length - strlen(v.file)),
      \   v.origin)})
      \ + [(s:tags.curidx > s:tags.length) ? '>' : '']

" PP text
" put =text

" :tags output
"   # VERS marqueur  DE ligne   dans le fichier/texte
"   1  1 gettagstack()@en     1  *tagsrch.txt*   For Vim version 8.2.  Last change: 2020 Dec 19
"   2  1 list-index@en    5897  eval.txt
"   3  1 tagstack@en      5923  eval.txt
" >
