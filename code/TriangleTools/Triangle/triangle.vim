let SessionLoad = 1
if &cp | set nocp | endif
let s:so_save = &so | let s:siso_save = &siso | set so=0 siso=0
let v:this_session=expand("<sfile>:p")
silent only
silent tabonly
cd ~/tmp/TriangleTools/Triangle
if expand('%') == '' && !&modified && line('$') <= 1 && getline(1) == ''
  let s:wipebuf = bufnr('%')
endif
set shortmess=aoO
badd +1 AbstractSyntaxTrees/AST.java
badd +0 AbstractSyntaxTrees/ActualParameter.java
badd +0 AbstractSyntaxTrees/ActualParameterSequence.java
badd +0 AbstractSyntaxTrees/AnyTypeDenoter.java
badd +0 AbstractSyntaxTrees/ArrayAggregate.java
badd +0 AbstractSyntaxTrees/ArrayExpression.java
badd +0 AbstractSyntaxTrees/ArrayTypeDenoter.java
badd +0 AbstractSyntaxTrees/AssignCommand.java
badd +0 AbstractSyntaxTrees/BinaryExpression.java
badd +0 AbstractSyntaxTrees/BinaryOperatorDeclaration.java
badd +0 AbstractSyntaxTrees/BoolTypeDenoter.java
badd +0 AbstractSyntaxTrees/CallCommand.java
badd +0 AbstractSyntaxTrees/CallExpression.java
badd +0 AbstractSyntaxTrees/CharTypeDenoter.java
badd +0 AbstractSyntaxTrees/CharacterExpression.java
badd +0 AbstractSyntaxTrees/CharacterLiteral.java
badd +0 AbstractSyntaxTrees/Command.java
badd +0 AbstractSyntaxTrees/ConstActualParameter.java
badd +0 AbstractSyntaxTrees/ConstDeclaration.java
badd +0 AbstractSyntaxTrees/ConstFormalParameter.java
badd +0 AbstractSyntaxTrees/Declaration.java
badd +0 AbstractSyntaxTrees/DotVname.java
badd +0 AbstractSyntaxTrees/EmptyActualParameterSequence.java
badd +0 AbstractSyntaxTrees/EmptyCommand.java
badd +0 AbstractSyntaxTrees/EmptyExpression.java
badd +0 AbstractSyntaxTrees/EmptyFormalParameterSequence.java
badd +0 AbstractSyntaxTrees/ErrorTypeDenoter.java
badd +0 AbstractSyntaxTrees/Expression.java
badd +0 AbstractSyntaxTrees/FieldTypeDenoter.java
badd +0 AbstractSyntaxTrees/FormalParameter.java
badd +0 AbstractSyntaxTrees/FormalParameterSequence.java
badd +0 AbstractSyntaxTrees/FuncActualParameter.java
badd +0 AbstractSyntaxTrees/FuncDeclaration.java
badd +0 AbstractSyntaxTrees/FuncFormalParameter.java
badd +0 AbstractSyntaxTrees/Identifier.java
badd +0 AbstractSyntaxTrees/IfCommand.java
badd +0 AbstractSyntaxTrees/IfExpression.java
badd +0 AbstractSyntaxTrees/IntTypeDenoter.java
badd +0 AbstractSyntaxTrees/IntegerExpression.java
badd +0 AbstractSyntaxTrees/IntegerLiteral.java
badd +0 AbstractSyntaxTrees/LetCommand.java
badd +0 AbstractSyntaxTrees/LetExpression.java
badd +0 AbstractSyntaxTrees/MultipleActualParameterSequence.java
badd +0 AbstractSyntaxTrees/MultipleArrayAggregate.java
badd +0 AbstractSyntaxTrees/MultipleFieldTypeDenoter.java
badd +0 AbstractSyntaxTrees/MultipleFormalParameterSequence.java
badd +0 AbstractSyntaxTrees/MultipleRecordAggregate.java
badd +0 AbstractSyntaxTrees/Operator.java
badd +0 AbstractSyntaxTrees/ProcActualParameter.java
badd +0 AbstractSyntaxTrees/ProcDeclaration.java
badd +0 AbstractSyntaxTrees/ProcFormalParameter.java
badd +0 AbstractSyntaxTrees/Program.java
badd +0 AbstractSyntaxTrees/RecordAggregate.java
badd +0 AbstractSyntaxTrees/RecordExpression.java
badd +0 AbstractSyntaxTrees/RecordTypeDenoter.java
badd +0 AbstractSyntaxTrees/SequentialCommand.java
badd +0 AbstractSyntaxTrees/SequentialDeclaration.java
badd +0 AbstractSyntaxTrees/SimpleTypeDenoter.java
badd +0 AbstractSyntaxTrees/SimpleVname.java
badd +0 AbstractSyntaxTrees/SingleActualParameterSequence.java
badd +0 AbstractSyntaxTrees/SingleArrayAggregate.java
badd +0 AbstractSyntaxTrees/SingleFieldTypeDenoter.java
badd +0 AbstractSyntaxTrees/SingleFormalParameterSequence.java
badd +0 AbstractSyntaxTrees/SingleRecordAggregate.java
badd +0 AbstractSyntaxTrees/SubscriptVname.java
badd +0 AbstractSyntaxTrees/Terminal.java
badd +0 AbstractSyntaxTrees/TypeDeclaration.java
badd +0 AbstractSyntaxTrees/TypeDenoter.java
badd +0 AbstractSyntaxTrees/UnaryExpression.java
badd +0 AbstractSyntaxTrees/UnaryOperatorDeclaration.java
badd +0 AbstractSyntaxTrees/VarActualParameter.java
badd +0 AbstractSyntaxTrees/VarDeclaration.java
badd +0 AbstractSyntaxTrees/VarFormalParameter.java
badd +0 AbstractSyntaxTrees/Visitor.java
badd +0 AbstractSyntaxTrees/Vname.java
badd +0 AbstractSyntaxTrees/VnameExpression.java
badd +0 AbstractSyntaxTrees/WhileCommand.java
badd +22 CodeGenerator/Encoder.java
badd +0 CodeGenerator/EqualityRoutine.java
badd +0 CodeGenerator/Field.java
badd +0 CodeGenerator/Frame.java
badd +0 CodeGenerator/KnownAddress.java
badd +0 CodeGenerator/KnownRoutine.java
badd +0 CodeGenerator/KnownValue.java
badd +0 CodeGenerator/ObjectAddress.java
badd +0 CodeGenerator/PrimitiveRoutine.java
badd +0 CodeGenerator/RuntimeEntity.java
badd +0 CodeGenerator/TypeRepresentation.java
badd +0 CodeGenerator/UnknownAddress.java
badd +0 CodeGenerator/UnknownRoutine.java
badd +0 CodeGenerator/UnknownValue.java
badd +0 Compiler.java
badd +22 ContextualAnalyzer/Checker.java
badd +0 ContextualAnalyzer/IdEntry.java
badd +0 ContextualAnalyzer/IdentificationTable.java
badd +0 ErrorReporter.java
badd +20 StdEnvironment.java
badd +0 SyntacticAnalyzer/Parser.java
badd +0 SyntacticAnalyzer/Scanner.java
badd +0 SyntacticAnalyzer/SourceFile.java
badd +0 SyntacticAnalyzer/SourcePosition.java
badd +0 SyntacticAnalyzer/SyntaxError.java
badd +0 SyntacticAnalyzer/Token.java
badd +0 TreeDrawer/Drawer.java
badd +0 TreeDrawer/DrawerFrame.java
badd +0 TreeDrawer/DrawerPanel.java
badd +0 TreeDrawer/DrawingTree.java
badd +0 TreeDrawer/LayoutVisitor.java
badd +0 TreeDrawer/Polygon.java
badd +0 TreeDrawer/Polyline.java
badd +1 ~/tmp/simpleAST/src/miniArith/SyntacticAnalyzer/Scanner.java
argglobal
silent! argdel *
$argadd AbstractSyntaxTrees/AST.java
$argadd AbstractSyntaxTrees/ActualParameter.java
$argadd AbstractSyntaxTrees/ActualParameterSequence.java
$argadd AbstractSyntaxTrees/AnyTypeDenoter.java
$argadd AbstractSyntaxTrees/ArrayAggregate.java
$argadd AbstractSyntaxTrees/ArrayExpression.java
$argadd AbstractSyntaxTrees/ArrayTypeDenoter.java
$argadd AbstractSyntaxTrees/AssignCommand.java
$argadd AbstractSyntaxTrees/BinaryExpression.java
$argadd AbstractSyntaxTrees/BinaryOperatorDeclaration.java
$argadd AbstractSyntaxTrees/BoolTypeDenoter.java
$argadd AbstractSyntaxTrees/CallCommand.java
$argadd AbstractSyntaxTrees/CallExpression.java
$argadd AbstractSyntaxTrees/CharTypeDenoter.java
$argadd AbstractSyntaxTrees/CharacterExpression.java
$argadd AbstractSyntaxTrees/CharacterLiteral.java
$argadd AbstractSyntaxTrees/Command.java
$argadd AbstractSyntaxTrees/ConstActualParameter.java
$argadd AbstractSyntaxTrees/ConstDeclaration.java
$argadd AbstractSyntaxTrees/ConstFormalParameter.java
$argadd AbstractSyntaxTrees/Declaration.java
$argadd AbstractSyntaxTrees/DotVname.java
$argadd AbstractSyntaxTrees/EmptyActualParameterSequence.java
$argadd AbstractSyntaxTrees/EmptyCommand.java
$argadd AbstractSyntaxTrees/EmptyExpression.java
$argadd AbstractSyntaxTrees/EmptyFormalParameterSequence.java
$argadd AbstractSyntaxTrees/ErrorTypeDenoter.java
$argadd AbstractSyntaxTrees/Expression.java
$argadd AbstractSyntaxTrees/FieldTypeDenoter.java
$argadd AbstractSyntaxTrees/FormalParameter.java
$argadd AbstractSyntaxTrees/FormalParameterSequence.java
$argadd AbstractSyntaxTrees/FuncActualParameter.java
$argadd AbstractSyntaxTrees/FuncDeclaration.java
$argadd AbstractSyntaxTrees/FuncFormalParameter.java
$argadd AbstractSyntaxTrees/Identifier.java
$argadd AbstractSyntaxTrees/IfCommand.java
$argadd AbstractSyntaxTrees/IfExpression.java
$argadd AbstractSyntaxTrees/IntTypeDenoter.java
$argadd AbstractSyntaxTrees/IntegerExpression.java
$argadd AbstractSyntaxTrees/IntegerLiteral.java
$argadd AbstractSyntaxTrees/LetCommand.java
$argadd AbstractSyntaxTrees/LetExpression.java
$argadd AbstractSyntaxTrees/MultipleActualParameterSequence.java
$argadd AbstractSyntaxTrees/MultipleArrayAggregate.java
$argadd AbstractSyntaxTrees/MultipleFieldTypeDenoter.java
$argadd AbstractSyntaxTrees/MultipleFormalParameterSequence.java
$argadd AbstractSyntaxTrees/MultipleRecordAggregate.java
$argadd AbstractSyntaxTrees/Operator.java
$argadd AbstractSyntaxTrees/ProcActualParameter.java
$argadd AbstractSyntaxTrees/ProcDeclaration.java
$argadd AbstractSyntaxTrees/ProcFormalParameter.java
$argadd AbstractSyntaxTrees/Program.java
$argadd AbstractSyntaxTrees/RecordAggregate.java
$argadd AbstractSyntaxTrees/RecordExpression.java
$argadd AbstractSyntaxTrees/RecordTypeDenoter.java
$argadd AbstractSyntaxTrees/SequentialCommand.java
$argadd AbstractSyntaxTrees/SequentialDeclaration.java
$argadd AbstractSyntaxTrees/SimpleTypeDenoter.java
$argadd AbstractSyntaxTrees/SimpleVname.java
$argadd AbstractSyntaxTrees/SingleActualParameterSequence.java
$argadd AbstractSyntaxTrees/SingleArrayAggregate.java
$argadd AbstractSyntaxTrees/SingleFieldTypeDenoter.java
$argadd AbstractSyntaxTrees/SingleFormalParameterSequence.java
$argadd AbstractSyntaxTrees/SingleRecordAggregate.java
$argadd AbstractSyntaxTrees/SubscriptVname.java
$argadd AbstractSyntaxTrees/Terminal.java
$argadd AbstractSyntaxTrees/TypeDeclaration.java
$argadd AbstractSyntaxTrees/TypeDenoter.java
$argadd AbstractSyntaxTrees/UnaryExpression.java
$argadd AbstractSyntaxTrees/UnaryOperatorDeclaration.java
$argadd AbstractSyntaxTrees/VarActualParameter.java
$argadd AbstractSyntaxTrees/VarDeclaration.java
$argadd AbstractSyntaxTrees/VarFormalParameter.java
$argadd AbstractSyntaxTrees/Visitor.java
$argadd AbstractSyntaxTrees/Vname.java
$argadd AbstractSyntaxTrees/VnameExpression.java
$argadd AbstractSyntaxTrees/WhileCommand.java
$argadd CodeGenerator/Encoder.java
$argadd CodeGenerator/EqualityRoutine.java
$argadd CodeGenerator/Field.java
$argadd CodeGenerator/Frame.java
$argadd CodeGenerator/KnownAddress.java
$argadd CodeGenerator/KnownRoutine.java
$argadd CodeGenerator/KnownValue.java
$argadd CodeGenerator/ObjectAddress.java
$argadd CodeGenerator/PrimitiveRoutine.java
$argadd CodeGenerator/RuntimeEntity.java
$argadd CodeGenerator/TypeRepresentation.java
$argadd CodeGenerator/UnknownAddress.java
$argadd CodeGenerator/UnknownRoutine.java
$argadd CodeGenerator/UnknownValue.java
$argadd Compiler.java
$argadd ContextualAnalyzer/Checker.java
$argadd ContextualAnalyzer/IdEntry.java
$argadd ContextualAnalyzer/IdentificationTable.java
$argadd ErrorReporter.java
$argadd SyntacticAnalyzer/Parser.java
$argadd SyntacticAnalyzer/Scanner.java
$argadd SyntacticAnalyzer/SourceFile.java
$argadd SyntacticAnalyzer/SourcePosition.java
$argadd SyntacticAnalyzer/SyntaxError.java
$argadd SyntacticAnalyzer/Token.java
$argadd TreeDrawer/Drawer.java
$argadd TreeDrawer/DrawerFrame.java
$argadd TreeDrawer/DrawerPanel.java
$argadd TreeDrawer/DrawingTree.java
$argadd TreeDrawer/LayoutVisitor.java
$argadd TreeDrawer/Polygon.java
$argadd TreeDrawer/Polyline.java
edit StdEnvironment.java
set splitbelow splitright
set nosplitbelow
set nosplitright
wincmd t
set winminheight=0
set winheight=1
set winminwidth=0
set winwidth=1
argglobal
2argu
if bufexists('StdEnvironment.java') | buffer StdEnvironment.java | else | edit StdEnvironment.java | endif
setlocal fdm=marker
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal nofen
let s:l = 19 - ((18 * winheight(0) + 23) / 46)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
19
normal! 0
tabnext 1
if exists('s:wipebuf') && len(win_findbuf(s:wipebuf)) == 0
  silent exe 'bwipe ' . s:wipebuf
endif
unlet! s:wipebuf
set winheight=1 winwidth=20 shortmess=filnxtToO
set winminheight=1 winminwidth=1
let s:sx = expand("<sfile>:p:r")."x.vim"
if file_readable(s:sx)
  exe "source " . fnameescape(s:sx)
endif
let &so = s:so_save | let &siso = s:siso_save
nohlsearch
let g:this_session = v:this_session
let g:this_obsession = v:this_session
let g:this_obsession_status = 2
doautoall SessionLoadPost
unlet SessionLoad
" vim: set ft=vim :
