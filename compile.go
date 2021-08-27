package lua

import (
	"fmt"
	"math"
	"reflect"

	"github.com/yuin/gopher-lua/ast"
)

/* internal constants & structs  {{{ */

const maxRegisters = 200 // 本地变量数量最多 200 个, 这个也是函数参数数量的限制

type expContextType int

const (
	ecGlobal expContextType = iota // 这个表示当前环境是全局环境
	ecUpvalue
	ecLocal
	ecTable
	ecVararg // 可变变量, 对应的是 '...' 操作符
	ecMethod // 对象的方法, 函数参数会补足 self 变量
	ecNone
)

const regNotDefined = opMaxArgsA + 1
const labelNoJump = 0

type expcontext struct {
	ctype expContextType
	reg   int
	// varargopt >= 0: wants varargopt+1 results, i.e  a = func()
	// varargopt = -1: ignore results             i.e  func()
	// varargopt = -2: receive all results        i.e  a = {func()}
	varargopt int
}

// 赋值表达式使用的上下文
type assigncontext struct {
	ec       *expcontext
	keyrk    int
	valuerk  int
	keyks    bool
	needmove bool
}

type lblabels struct {
	t int
	f int
	e int
	b bool
}

type constLValueExpr struct {
	ast.ExprBase

	Value LValue
}

// }}}

/* utilities {{{ */
var _ecnone0 = &expcontext{ecNone, regNotDefined, 0}
var _ecnonem1 = &expcontext{ecNone, regNotDefined, -1}
var _ecnonem2 = &expcontext{ecNone, regNotDefined, -2}
var ecfuncdef = &expcontext{ecMethod, regNotDefined, 0}

func ecupdate(ec *expcontext, ctype expContextType, reg, varargopt int) {
	if ec == _ecnone0 || ec == _ecnonem1 || ec == _ecnonem2 {
		panic("can not update ec cache")
	}
	ec.ctype = ctype
	ec.reg = reg
	ec.varargopt = varargopt
}

func ecnone(varargopt int) *expcontext {
	switch varargopt {
	case 0:
		return _ecnone0
	case -1:
		return _ecnonem1
	case -2:
		return _ecnonem2
	}

	return &expcontext{ecNone, regNotDefined, varargopt}
}

func shouldmove(ec *expcontext, reg int) bool {
	return ec.ctype == ecLocal && ec.reg != regNotDefined && ec.reg != reg
}

func sline(pos ast.PositionHolder) int {
	return pos.Line()
}

func eline(pos ast.PositionHolder) int {
	return pos.LastLine()
}

func savereg(ec *expcontext, reg int) int {
	if ec.ctype != ecLocal || ec.reg == regNotDefined {
		return reg
	}
	return ec.reg
}

func raiseCompileError(context *funcContext, line int, format string, args ...interface{}) {
	msg := fmt.Sprintf(format, args...)
	panic(&CompileError{context: context, Line: line, Message: msg})
}

func isVarArgReturnExpr(expr ast.Expr) bool {
	switch ex := expr.(type) {
	case *ast.FuncCallExpr:
		return !ex.AdjustRet
	case *ast.Comma3Expr:
		return true
	}
	return false
}

func lnumberValue(expr ast.Expr) (LNumber, bool) {
	if ex, ok := expr.(*ast.NumberExpr); ok {
		lv, err := parseNumber(ex.Value)
		if err != nil {
			lv = LNumber(math.NaN())
		}
		return lv, true
	} else if ex, ok := expr.(*constLValueExpr); ok {
		return ex.Value.(LNumber), true
	}
	return 0, false
}

/* utilities }}} */

type CompileError struct { // {{{
	context *funcContext
	Line    int
	Message string
}

func (e *CompileError) Error() string {
	return fmt.Sprintf("compile error near line(%v) %v: %v", e.Line, e.context.Proto.SourceName, e.Message)
} // }}}

// codeStore 结构用来保存一段代码的字节码
type codeStore struct { // {{{
	codes []uint32 // 字节码
	lines []int    // 源码行相关信息
	pc    int      // 当前保存的 pc 指针, 这个指向 codes 里面下一个 可以用于保存数据的位置 - 严格来说这个不能叫 pc 吧
}

// 保存字节码, Add 开头的指令, 会导致 pc 往前移动
// inst 是字节码, line 是字节码对应的行数(多行的情况下, 用的是第一行)
func (cd *codeStore) Add(inst uint32, line int) {
	if l := len(cd.codes); l <= 0 || cd.pc == l {
		cd.codes = append(cd.codes, inst)
		cd.lines = append(cd.lines, line)
	} else {
		cd.codes[cd.pc] = inst
		cd.lines[cd.pc] = line
	}

	cd.pc++
}

func (cd *codeStore) AddABC(op int, a int, b int, c int, line int) {
	cd.Add(opCreateABC(op, a, b, c), line)
}

func (cd *codeStore) AddABx(op int, a int, bx int, line int) {
	cd.Add(opCreateABx(op, a, bx), line)
}

func (cd *codeStore) AddASbx(op int, a int, sbx int, line int) {
	cd.Add(opCreateASbx(op, a, sbx), line)
}

// TODO: 具体在理顺一下这里的逻辑
func (cd *codeStore) PropagateKMV(top int, save *int, reg *int, inc int) {
	lastinst := cd.Last()

	// 找到最顶上的那条指令, 然后找寄存器 A 的数据
	if opGetArgA(lastinst) >= top {
		// 如果寄存器 A 的数据, 比当前指定的 top 还大
		// 那么这条指令有可能是不可用的, 这样的话, 把操作数记录下来, 外部重新组织指令
		switch opGetOpCode(lastinst) {
		case OP_LOADK:
			// OP_LOADK A BX
			cindex := opGetArgBx(lastinst)
			if cindex <= opMaxIndexRk {
				cd.Pop()
				*save = opRkAsk(cindex)
				return
			}
		case OP_MOVE:
			cd.Pop()
			*save = opGetArgB(lastinst)
			return
		}
	}

	*save = *reg
	*reg = *reg + inc
}

func (cd *codeStore) PropagateMV(top int, save *int, reg *int, inc int) {
	lastinst := cd.Last()
	if opGetArgA(lastinst) >= top {
		switch opGetOpCode(lastinst) {
		case OP_MOVE:
			cd.Pop()
			*save = opGetArgB(lastinst)
			return
		}
	}
	*save = *reg
	*reg = *reg + inc
}

/*
** Create a OP_LOADNIL instruction, but try to optimize: if the previous
** instruction is also OP_LOADNIL and ranges are compatible, adjust
** range of previous instruction instead of emitting a new one. (For
** instance, 'local a; local b' will generate a single opcode.)
**
** R[A], R[A+1], ..., R[A+B] := nil
 */
func (cd *codeStore) AddLoadNil(a, b, line int) {
	last := cd.Last()
	if opGetOpCode(last) == OP_LOADNIL && (opGetArgA(last)+opGetArgB(last)) == a {
		// 这里表示前一个指令也是 OP_LOADNIL, 而且只赋值了一个 nil, 这里吧 b 追加上, 可以节省一条指令
		cd.SetB(cd.LastPC(), b)
	} else {
		cd.AddABC(OP_LOADNIL, a, b, 0, line)
	}
}

// Set 开头的都不会导致 pc 增加
func (cd *codeStore) SetOpCode(pc int, v int) {
	opSetOpCode(&cd.codes[pc], v)
}

func (cd *codeStore) SetA(pc int, v int) {
	opSetArgA(&cd.codes[pc], v)
}

func (cd *codeStore) SetB(pc int, v int) {
	opSetArgB(&cd.codes[pc], v)
}

func (cd *codeStore) SetC(pc int, v int) {
	opSetArgC(&cd.codes[pc], v)
}

func (cd *codeStore) SetBx(pc int, v int) {
	opSetArgBx(&cd.codes[pc], v)
}

func (cd *codeStore) SetSbx(pc int, v int) {
	opSetArgSbx(&cd.codes[pc], v)
}

// 取出 pc 位置上的字节码
func (cd *codeStore) At(pc int) uint32 {
	return cd.codes[pc]
}

func (cd *codeStore) List() []uint32 {
	return cd.codes[:cd.pc]
}

func (cd *codeStore) PosList() []int {
	return cd.lines[:cd.pc]
}

func (cd *codeStore) LastPC() int {
	return cd.pc - 1
}

func (cd *codeStore) Last() uint32 {
	if cd.pc == 0 {
		return opInvalidInstruction
	}

	return cd.codes[cd.pc-1]
}

func (cd *codeStore) Pop() {
	cd.pc--
} /* }}} Code */

/* {{{ VarNamePool */

// 这里两个结构定义了使用到的变量名 - 变量值之间的关系

// 此结构表示在变量符号表 Index 位置的变量, 名字是 Name
type varNamePoolValue struct {
	Index int
	Name  string
}

// 变量池看上去像这个样子(-R- 表示这个位置预留了, 这个图里留了 2):
// 有这个保留的用处是, 在其他的函数栈帧里面, 前面的位置已经被使用了
//
// | -R- | -R- | A | B | C | D | E | ...
type varNamePool struct {
	names  []string // 存储变量名称
	offset int      // 表示从 names 最前面预留多少空间不用
}

func newVarNamePool(offset int) *varNamePool {
	return &varNamePool{make([]string, 0, 16), offset}
}

func (vp *varNamePool) Names() []string {
	return vp.names
}

func (vp *varNamePool) List() []varNamePoolValue {
	result := make([]varNamePoolValue, len(vp.names), len(vp.names))
	for i, name := range vp.names {
		result[i].Index = i + vp.offset
		result[i].Name = name
	}

	return result
}

func (vp *varNamePool) LastIndex() int {
	return vp.offset + len(vp.names)
}

func (vp *varNamePool) Find(name string) int {
	for i := len(vp.names) - 1; i >= 0; i-- {
		if vp.names[i] == name {
			return i + vp.offset
		}
	}

	return -1
}

// 在变量表里面查找 name, 如果有即返回相应的 index
// 如果没有, 则存入 name, 并返回其位置
func (vp *varNamePool) RegisterUnique(name string) int {
	index := vp.Find(name)
	if index < 0 {
		return vp.Register(name)
	}
	return index
}

// 在变量表里面存入 name 并返回它所在的位置
// 注意注册只是注册, 不是赋值.
// 编译时不知道赋值是多少, 只有在运行时才能知道
func (vp *varNamePool) Register(name string) int {
	vp.names = append(vp.names, name)
	return len(vp.names) - 1 + vp.offset
}

/* }}} VarNamePool */

/* FuncContext {{{ */

// 代码块的表示结构
type codeBlock struct {
	LocalVars  *varNamePool
	BreakLabel int
	Parent     *codeBlock
	RefUpvalue bool
	LineStart  int
	LastLine   int
}

func newCodeBlock(localvars *varNamePool, blabel int, parent *codeBlock, pos ast.PositionHolder) *codeBlock {
	bl := &codeBlock{localvars, blabel, parent, false, 0, 0}
	if pos != nil {
		bl.LineStart = pos.Line()
		bl.LastLine = pos.LastLine()
	}

	return bl
}

// 函数上下文
type funcContext struct {
	Proto    *FunctionProto // 函数原型信息
	Code     *codeStore     // 代码块对应的二进制码
	Parent   *funcContext   // 父级代码块上下文
	Upvalues *varNamePool   // 代码块的 upvalues 符号表
	Block    *codeBlock     // TODO
	Blocks   []*codeBlock   // TODO: Block 栈 -- 应该是运行时追踪代码块用的
	regTop   int
	labelId  int
	labelPc  map[int]int
}

func newFuncContext(sourcename string, parent *funcContext) *funcContext {
	fc := &funcContext{
		Proto:    newFunctionProto(sourcename),
		Code:     &codeStore{make([]uint32, 0, 1024), make([]int, 0, 1024), 0},
		Parent:   parent,
		Upvalues: newVarNamePool(0),
		Block:    newCodeBlock(newVarNamePool(0), labelNoJump, nil, nil),
		regTop:   0,
		labelId:  1,
		labelPc:  map[int]int{},
	}

	fc.Blocks = []*codeBlock{fc.Block}
	return fc
}

// label 是代码中的控制结构, 比方说 if/else 等
func (fc *funcContext) NewLabel() int {
	ret := fc.labelId
	fc.labelId++
	return ret
}

func (fc *funcContext) SetLabelPc(label int, pc int) {
	fc.labelPc[label] = pc
}

func (fc *funcContext) GetLabelPc(label int) int {
	return fc.labelPc[label]
}

// 找到 value 对应的常量在常量表里面的索引
func (fc *funcContext) ConstIndex(value LValue) int {
	ctype := value.Type()
	for i, lv := range fc.Proto.Constants {
		if lv.Type() == ctype && lv == value {
			return i
		}
	}

	// 没找到的情况下, 追加进去, 并返回这个索引
	fc.Proto.Constants = append(fc.Proto.Constants, value)
	v := len(fc.Proto.Constants) - 1
	if v > opMaxArgBx {
		raiseCompileError(fc, fc.Proto.LineDefined, "too many constants")
	}

	return v
}

// 在变量符号表注册 name 变量
func (fc *funcContext) RegisterLocalVar(name string) int {
	ret := fc.Block.LocalVars.Register(name)
	fc.Proto.DbgLocals = append(fc.Proto.DbgLocals, &DbgLocalInfo{Name: name, StartPc: fc.Code.LastPC() + 1})
	fc.SetRegTop(fc.RegTop() + 1)
	return ret
}

// 在函数环境的变量作用域中找出 name 对应的变量位置
// 查找规则从当前代码块开始, 逐级向上查询, 找不到即返回 -1
func (fc *funcContext) FindLocalVarAndBlock(name string) (int, *codeBlock) {
	for block := fc.Block; block != nil; block = block.Parent {
		if index := block.LocalVars.Find(name); index > -1 {
			return index, block
		}
	}

	return -1, nil
}

// 返回符号在符号表索引
func (fc *funcContext) FindLocalVar(name string) int {
	idx, _ := fc.FindLocalVarAndBlock(name)
	return idx
}

// 将本地符号表里面的符号-索引组合以列表形式返回
func (fc *funcContext) LocalVars() []varNamePoolValue {
	result := make([]varNamePoolValue, 0, 32)
	for _, block := range fc.Blocks {
		result = append(result, block.LocalVars.List()...)
	}

	return result
}

// 函数进入代码块的时候, 执行这个操作.
// 可以看到  newVarNamePool 的 offset 被设置成现在符号表的栈顶
func (fc *funcContext) EnterBlock(blabel int, pos ast.PositionHolder) {
	fc.Block = newCodeBlock(newVarNamePool(fc.RegTop()), blabel, fc.Block, pos)
	fc.Blocks = append(fc.Blocks, fc.Block)
}

// TODO: upvalues ???
// upvalues 应该是闭包对外部的引用
func (fc *funcContext) CloseUpvalues() int {
	n := -1

	if fc.Block.RefUpvalue {
		// 这里遍历父代码块的局部变量列表, 并将他们销毁
		// TODO: 具体的销毁操作是什么样子的呢?
		n = fc.Block.Parent.LocalVars.LastIndex()
		fc.Code.AddABC(OP_CLOSE, n, 0, 0, fc.Block.LastLine)
	}

	return n
}

// 结束代码块的操作
func (fc *funcContext) LeaveBlock() int {
	closed := fc.CloseUpvalues()
	fc.EndScope()
	fc.Block = fc.Block.Parent
	fc.SetRegTop(fc.Block.LocalVars.LastIndex()) // 注意这里, 代码块的局部变量就被销毁了
	return closed
}

func (fc *funcContext) EndScope() {
	// 这里标记了一下每个变量作用域的结束 pc 位置
	for _, vr := range fc.Block.LocalVars.List() {
		fc.Proto.DbgLocals[vr.Index].EndPc = fc.Code.LastPC()
	}
}

func (fc *funcContext) SetRegTop(top int) {
	if top > maxRegisters {
		raiseCompileError(fc, fc.Proto.LineDefined, "too many local variables")
	}

	fc.regTop = top
}

func (fc *funcContext) RegTop() int {
	return fc.regTop
}

/* FuncContext }}} */

// block 实际上就是 chunk, 区别在于 block 编译会为 block 设置专门的作用域, chunk 则没有

// 编译代码语句, 逐个语句编译
func compileChunk(context *funcContext, chunk []ast.Stmt) { // {{{
	for _, stmt := range chunk {
		compileStmt(context, stmt)
	}
} // }}}

// 编译代码块
func compileBlock(context *funcContext, chunk []ast.Stmt) { // {{{
	if len(chunk) == 0 {
		return
	}

	ph := &ast.Node{}
	ph.SetLine(sline(chunk[0]))
	ph.SetLastLine(eline(chunk[len(chunk)-1]))
	context.EnterBlock(labelNoJump, ph)
	for _, stmt := range chunk {
		compileStmt(context, stmt)
	}

	context.LeaveBlock()
} // }}}

// 这里编译单条语句. 每种语句都有自己不同的字节码生成方式
func compileStmt(context *funcContext, stmt ast.Stmt) { // {{{
	switch st := stmt.(type) {
	case *ast.AssignStmt:
		compileAssignStmt(context, st)
	case *ast.LocalAssignStmt:
		compileLocalAssignStmt(context, st)
	case *ast.FuncCallStmt:
		compileFuncCallExpr(context, context.RegTop(), st.Expr.(*ast.FuncCallExpr), ecnone(-1))
	case *ast.DoBlockStmt:
		context.EnterBlock(labelNoJump, st)
		compileChunk(context, st.Stmts)
		context.LeaveBlock()
	case *ast.WhileStmt:
		compileWhileStmt(context, st)
	case *ast.RepeatStmt:
		compileRepeatStmt(context, st)
	case *ast.FuncDefStmt:
		compileFuncDefStmt(context, st)
	case *ast.ReturnStmt:
		compileReturnStmt(context, st)
	case *ast.IfStmt:
		compileIfStmt(context, st)
	case *ast.BreakStmt:
		compileBreakStmt(context, st)
	case *ast.NumberForStmt:
		compileNumberForStmt(context, st)
	case *ast.GenericForStmt:
		compileGenericForStmt(context, st)
	}
} // }}}

// 编译赋值表达式, 左半部分
func compileAssignStmtLeft(context *funcContext, stmt *ast.AssignStmt) (int, []*assigncontext) { // {{{
	reg := context.RegTop() // 这是找到当前变量符号表的顶部位置, 后面的变量存储就放在这后面
	acs := make([]*assigncontext, 0, len(stmt.Lhs))

	// 遍历左边的表达式
	for i, lhs := range stmt.Lhs {
		islast := i == len(stmt.Lhs)-1
		switch st := lhs.(type) {
		case *ast.IdentExpr: // 标识符
			identtype := getIdentRefType(context, context, st)
			ec := &expcontext{identtype, regNotDefined, 0}
			switch identtype {
			case ecGlobal:
				// 全局变量, 在符号表里面找到该变量
				context.ConstIndex(LString(st.Value))
			case ecUpvalue:
				// 闭包引用变量
				// TODO: 事实上 st.Value 对应的变量应该是一定存在的, 这里这句话是不是可以免掉?
				context.Upvalues.RegisterUnique(st.Value)
			case ecLocal:
				if islast {
					// 如果是变量列表中最后一个变量, 那么将当前表达式环境中的变量符号表指针设置到 reg 成员
					// TODO: reg 成员都是怎么用的?
					ec.reg = context.FindLocalVar(st.Value)
				}
			}

			acs = append(acs, &assigncontext{ec, 0, 0, false, false})
		case *ast.AttrGetExpr: // 成员变量
			// 成员一定是来自 table 的, 因此赋值环境上下文使用了 ecTable
			ec := &expcontext{ecTable, regNotDefined, 0}
			ac := &assigncontext{ec, 0, 0, false, false}

			// 1. 处理 object 信息, 运行时对应的字节码执行完成之后, object 对象就在栈顶了
			// TODO: 确定对于运行时的理解是不是对的
			compileExprWithKMVPropagation(context, st.Object, &reg, &ac.ec.reg)

			// 2. 这里实际上就是在计算 object.member 这个表达式了.
			// TODO: 运行时执行完, 栈上面会留什么呢?
			ac.keyrk = reg
			reg += compileExpr(context, reg, st.Key, ecnone(0))
			if _, ok := st.Key.(*ast.StringExpr); ok {
				ac.keyks = true
			}

			acs = append(acs, ac)

		default:
			// 其他情况的左值是不合法的
			panic("invalid left expression.")
		}
	}
	return reg, acs
} // }}}

// 赋值表达式的右半部分
func compileAssignStmtRight(context *funcContext, stmt *ast.AssignStmt, reg int, acs []*assigncontext) (int, []*assigncontext) { // {{{
	lennames := len(stmt.Lhs)
	lenexprs := len(stmt.Rhs)
	namesassigned := 0

	// 遍历左值列表, 为每个左值对应的变量赋值
	for namesassigned < lennames {
		ac := acs[namesassigned] // 这个 asc 是在左值列表处理的时候就计算好了
		ec := ac.ec              // 表达式的上下文
		var expr ast.Expr = nil

		// 出现左值数量大于右值数量的情况, 多出来的左值需要被补齐值 = nil
		if namesassigned >= lenexprs {
			expr = &ast.NilExpr{}
			expr.SetLine(sline(stmt.Lhs[namesassigned]))
			expr.SetLastLine(eline(stmt.Lhs[namesassigned]))
		} else if isVarArgReturnExpr(stmt.Rhs[namesassigned]) && (lenexprs-namesassigned-1) <= 0 {
			// 这个 if 块是说, 最后一个右值是函数调用或者是 '...' 操作符
			// 注意只有最后一个函数调用的多个返回值, 才会被处理为右值列表中的数据. 非末尾位置的, 处理为右值列表中的一个值

			// 1. 找到右值列表里面缺失的表达式数量
			// 2. 计算该右值表达式
			// 3. 这个右值表达式比较特殊, 会导致处理循环退出
			varargopt := lennames - namesassigned - 1
			regstart := reg
			reginc := compileExpr(context, reg, stmt.Rhs[namesassigned], ecnone(varargopt))
			reg += reginc
			for i := namesassigned; i < namesassigned+int(reginc); i++ {
				acs[i].needmove = true // TODO: 这是干啥的?
				if acs[i].ec.ctype == ecTable {
					acs[i].valuerk = regstart + (i - namesassigned)
				}
			}
			namesassigned = lennames
			continue
		}

		if expr == nil {
			expr = stmt.Rhs[namesassigned]
		}

		// 编译右值表达式
		idx := reg
		reginc := compileExpr(context, reg, expr, ec)
		if ec.ctype == ecTable {
			if _, ok := expr.(*ast.LogicalOpExpr); !ok {
				context.Code.PropagateKMV(context.RegTop(), &ac.valuerk, &reg, reginc)
			} else {
				ac.valuerk = idx
				reg += reginc
			}
		} else {
			ac.needmove = reginc != 0
			reg += reginc
		}
		namesassigned += 1
	}

	rightreg := reg - 1

	// extra right exprs
	// 多出来的右值被忽略掉, 但是这些表达式依然会被编译为字节码处理一遍
	for i := namesassigned; i < lenexprs; i++ {
		varargopt := -1
		if i != lenexprs-1 {
			varargopt = 0
		}
		reg += compileExpr(context, reg, stmt.Rhs[i], ecnone(varargopt))
	}

	return rightreg, acs
} // }}}

// 赋值表达式转编译
func compileAssignStmt(context *funcContext, stmt *ast.AssignStmt) { // {{{
	code := context.Code

	lennames := len(stmt.Lhs) // 变量数目

	reg, acs := compileAssignStmtLeft(context, stmt)
	reg, acs = compileAssignStmtRight(context, stmt, reg, acs)

	for i := lennames - 1; i >= 0; i-- {
		ex := stmt.Lhs[i]
		switch acs[i].ec.ctype {
		case ecLocal:
			// 这里是在赋值表达式右值列表中有函数返回值或者 '...' 操作符场景时, 需要将计算好的右值, 移动到本地变量相应的位置
			if acs[i].needmove {
				code.AddABC(OP_MOVE, context.FindLocalVar(ex.(*ast.IdentExpr).Value), reg, 0, sline(ex))
				reg -= 1
			}
		case ecGlobal:
			code.AddABx(OP_SETGLOBAL, reg, context.ConstIndex(LString(ex.(*ast.IdentExpr).Value)), sline(ex))
			reg -= 1
		case ecUpvalue:
			code.AddABC(OP_SETUPVAL, reg, context.Upvalues.RegisterUnique(ex.(*ast.IdentExpr).Value), 0, sline(ex))
			reg -= 1
		case ecTable:
			opcode := OP_SETTABLE
			if acs[i].keyks {
				opcode = OP_SETTABLEKS
			}
			code.AddABC(opcode, acs[i].ec.reg, acs[i].keyrk, acs[i].valuerk, sline(ex))
			if !opIsK(acs[i].valuerk) {
				reg -= 1
			}
		}
	}
} // }}}

func compileRegAssignment(context *funcContext, names []string, exprs []ast.Expr, reg int, nvars int, line int) { // {{{
	lennames := len(names)
	lenexprs := len(exprs)
	namesassigned := 0
	ec := &expcontext{}

	for namesassigned < lennames && namesassigned < lenexprs {
		if isVarArgReturnExpr(exprs[namesassigned]) && (lenexprs-namesassigned-1) <= 0 {

			varargopt := nvars - namesassigned
			ecupdate(ec, ecVararg, reg, varargopt-1)
			compileExpr(context, reg, exprs[namesassigned], ec)
			reg += varargopt
			namesassigned = lennames
		} else {
			ecupdate(ec, ecLocal, reg, 0)
			compileExpr(context, reg, exprs[namesassigned], ec)
			reg += 1
			namesassigned += 1
		}
	}

	// extra left names
	if lennames > namesassigned {
		restleft := lennames - namesassigned - 1
		context.Code.AddLoadNil(reg, reg+restleft, line)
		reg += restleft
	}

	// extra right exprs
	for i := namesassigned; i < lenexprs; i++ {
		varargopt := -1
		if i != lenexprs-1 {
			varargopt = 0
		}

		ecupdate(ec, ecNone, reg, varargopt)
		reg += compileExpr(context, reg, exprs[i], ec)
	}
} // }}}

func compileLocalAssignStmt(context *funcContext, stmt *ast.LocalAssignStmt) { // {{{
	reg := context.RegTop()

	// 这里是处理将匿名函数赋值给变量的逻辑
	// 处理逻辑和正常逻辑是一样的啊, 为啥要这么写?
	if len(stmt.Names) == 1 && len(stmt.Exprs) == 1 {
		if _, ok := stmt.Exprs[0].(*ast.FunctionExpr); ok {
			context.RegisterLocalVar(stmt.Names[0])
			compileRegAssignment(context, stmt.Names, stmt.Exprs, reg, len(stmt.Names), sline(stmt))
			return
		}
	}

	compileRegAssignment(context, stmt.Names, stmt.Exprs, reg, len(stmt.Names), sline(stmt))
	for _, name := range stmt.Names {
		context.RegisterLocalVar(name)
	}
} // }}}

func compileReturnStmt(context *funcContext, stmt *ast.ReturnStmt) { // {{{
	lenexprs := len(stmt.Exprs)
	code := context.Code
	reg := context.RegTop()
	a := reg
	lastisvaarg := false

	// 仅有单个返回值
	if lenexprs == 1 {
		switch ex := stmt.Exprs[0].(type) {
		case *ast.IdentExpr:
			if idx := context.FindLocalVar(ex.Value); idx > -1 {
				code.AddABC(OP_RETURN, idx, 2, 0, sline(stmt))
				return
			}
		case *ast.FuncCallExpr:
			reg += compileExpr(context, reg, ex, ecnone(-2))
			code.SetOpCode(code.LastPC(), OP_TAILCALL)
			code.AddABC(OP_RETURN, a, 0, 0, sline(stmt))
			return
		}
	}

	// 如果返回值是多个值(表达式)
	for i, expr := range stmt.Exprs {
		if i == lenexprs-1 && isVarArgReturnExpr(expr) {
			compileExpr(context, reg, expr, ecnone(-2))
			lastisvaarg = true
		} else {
			reg += compileExpr(context, reg, expr, ecnone(0))
		}
	}
	count := reg - a + 1
	if lastisvaarg {
		count = 0
	}

	context.Code.AddABC(OP_RETURN, a, count, 0, sline(stmt))
} // }}}

func compileIfStmt(context *funcContext, stmt *ast.IfStmt) { // {{{
	thenlabel := context.NewLabel()
	elselabel := context.NewLabel()
	endlabel := context.NewLabel()

	// 编译分支条件
	compileBranchCondition(context, context.RegTop(), stmt.Condition, thenlabel, elselabel, false)

	//  标记当前 pc 位置是一个 then 语句. 跳转指令在运行时会根据这些标记, 决定跳转到的 pc 值
	context.SetLabelPc(thenlabel, context.Code.LastPC())
	compileBlock(context, stmt.Then)
	if len(stmt.Else) > 0 {
		// 有 else 语句, 但是在执行完 then 块的时候, 希望能跳转到 end 的地方
		// 没有 else 的时候, 自然不需要跳转
		context.Code.AddASbx(OP_JMP, 0, endlabel, sline(stmt))
	}

	context.SetLabelPc(elselabel, context.Code.LastPC())
	if len(stmt.Else) > 0 {
		compileBlock(context, stmt.Else)
		context.SetLabelPc(endlabel, context.Code.LastPC())
	}

} // }}}

// hasnextcond 参数表示这个条件语句是不是有多个条件语句组成的, 这种情况只有解析到最后一个能确定跳转的跳转语句时候, 才可以确定具体的跳转字节码
// 本函数根据 expr 表达式, 生成跳转代码.
// Lua 的 if-else 语句跳转是判断条件是不是假(跳转 else)
// TODO: 感觉这里的实现有点复杂, 看一下官方是怎么实现的
func compileBranchCondition(context *funcContext, reg int, expr ast.Expr, thenlabel, elselabel int, hasnextcond bool) { // {{{
	// TODO folding constants?
	code := context.Code
	flip := 0
	jumplabel := elselabel
	if hasnextcond {
		flip = 1
		// 还有后续条件要计算, 那么在当前条件执行为真的情况下, 跳转到接下来的位置继续计算
		jumplabel = thenlabel
	}

	switch ex := expr.(type) {
	case *ast.FalseExpr, *ast.NilExpr:
		if !hasnextcond {
			// 条件为假, 且没有后续的条件了
			code.AddASbx(OP_JMP, 0, elselabel, sline(expr))
			return
		}
	case *ast.TrueExpr, *ast.NumberExpr, *ast.StringExpr:
		if !hasnextcond {
			// 条件是真, 则什么都不需要做
			return
		}
	case *ast.UnaryNotOpExpr:
		// 1. OR 条件: 要求了 hasnextcode.
		// 如果这里 ex.Expr 为假(Not ex 为真), 此时不在需要计算后续条件(跳到 thenlabel 执行)
		// 如果这里 ex.Expr 为真(Not ex 为假), 此时还需要计算后续条件(跳到 thenlabel 执行)
		// 上文中 hasnextcode 要求了, 这里传入不要求, compileBranchCondition 就可以全部执行到 thenlabel
		//
		// 2. 非 OR 条件. 那就是 AND, 或者没有逻辑关系条件(与 AND 一样的处理)
		//    接下来的讨论, 没有要求 hasnectcode, 那么传入 !hasnextcond
		// 如果计算得到 ex.Expr 为真(Not ex 为假), 则无需继续计算后面的条件, 跳转直接到达 elselabel -- 实现了短路逻辑
		// 如果计算得到 ex.Expr 为假(Not ex 为真), 则需要继续计算后面的条件, 跳转的位置是 thenlabel ...
		compileBranchCondition(context, reg, ex.Expr, elselabel, thenlabel, !hasnextcond)
		return
	case *ast.LogicalOpExpr:
		// if a and b then ... else ... end
		// 这里面的复杂的跳转逻辑, 是在实现短路计算
		switch ex.Operator {
		case "and":
			nextcondlabel := context.NewLabel()
			// 先编译 lhs 条件. 当 lhs 不满足的时候, 可以直接调到 elselabel, 不需要计算 rhs
			compileBranchCondition(context, reg, ex.Lhs, nextcondlabel, elselabel, false)
			context.SetLabelPc(nextcondlabel, context.Code.LastPC()) // 修正 nextcondlabel 对应的 pc 位置
			// 现在尝试 rhs 条件, 此时说明 lhs 是真. 如果 rhs 是假, 就回跳转到 elselabel
			compileBranchCondition(context, reg, ex.Rhs, thenlabel, elselabel, hasnextcond) // cond b
		case "or":
			// nextcondlabel 是 rhs 条件的字节码开始位置, or 条件 lhs 为假, rhs 依旧要计算
			nextcondlabel := context.NewLabel()
			compileBranchCondition(context, reg, ex.Lhs, thenlabel, nextcondlabel, true)
			context.SetLabelPc(nextcondlabel, context.Code.LastPC())
			compileBranchCondition(context, reg, ex.Rhs, thenlabel, elselabel, hasnextcond)
		}
		return
	case *ast.RelationalOpExpr:
		// 处理关系表达式, jumplabel 表示关系为真的时候, 需要跳转到的执行位置
		compileRelationalOpExprAux(context, reg, ex, flip, jumplabel)
		return
	}

	a := reg
	// 条件表达式在上文已经编译完毕, 这里为其生成字节码, 最终会在栈上留下来执行结果
	compileExprWithMVPropagation(context, expr, &reg, &a)

	code.AddABC(OP_TEST, a, 0, 0^flip, sline(expr)) // OP_TEST 指令在栈上留下来测试结果
	code.AddASbx(OP_JMP, 0, jumplabel, sline(expr)) // OP_JMP 根据 OP_TEST 的结果执行跳转
} // }}}

func compileWhileStmt(context *funcContext, stmt *ast.WhileStmt) { // {{{
	thenlabel := context.NewLabel()
	elselabel := context.NewLabel()
	condlabel := context.NewLabel()

	context.SetLabelPc(condlabel, context.Code.LastPC())
	compileBranchCondition(context, context.RegTop(), stmt.Condition, thenlabel, elselabel, false)
	context.SetLabelPc(thenlabel, context.Code.LastPC())
	context.EnterBlock(elselabel, stmt)
	compileChunk(context, stmt.Stmts)
	context.CloseUpvalues()
	context.Code.AddASbx(OP_JMP, 0, condlabel, eline(stmt)) // 跳转到 condlabel 处, 重新执行条件检测
	context.LeaveBlock()
	context.SetLabelPc(elselabel, context.Code.LastPC())
} // }}}

func compileRepeatStmt(context *funcContext, stmt *ast.RepeatStmt) { // {{{
	initlabel := context.NewLabel()
	thenlabel := context.NewLabel()
	elselabel := context.NewLabel()

	context.SetLabelPc(initlabel, context.Code.LastPC())
	context.SetLabelPc(elselabel, context.Code.LastPC())
	context.EnterBlock(thenlabel, stmt)
	compileChunk(context, stmt.Stmts)
	compileBranchCondition(context, context.RegTop(), stmt.Condition, thenlabel, elselabel, false)

	context.SetLabelPc(thenlabel, context.Code.LastPC())
	n := context.LeaveBlock()

	// n 表示最后面的 upvalue 在符号表里面的索引.
	// 这里是说在用到了 upvalue 的 repeat 语句块里面, 使用完之后, 要将临时变量都销毁掉
	// TODO: 理解一下这个地方
	if n > -1 {
		label := context.NewLabel()
		context.Code.AddASbx(OP_JMP, 0, label, eline(stmt))
		context.SetLabelPc(elselabel, context.Code.LastPC())
		context.Code.AddABC(OP_CLOSE, n, 0, 0, eline(stmt)) // >= n 的变量都销毁
		context.Code.AddASbx(OP_JMP, 0, initlabel, eline(stmt))
		context.SetLabelPc(label, context.Code.LastPC())
	}

} // }}}

func compileBreakStmt(context *funcContext, stmt *ast.BreakStmt) { // {{{
	for block := context.Block; block != nil; block = block.Parent {
		if label := block.BreakLabel; label != labelNoJump {
			if block.RefUpvalue {
				context.Code.AddABC(OP_CLOSE, block.Parent.LocalVars.LastIndex(), 0, 0, sline(stmt))
			}

			context.Code.AddASbx(OP_JMP, 0, label, sline(stmt))
			return
		}
	}

	raiseCompileError(context, sline(stmt), "no loop to break")
} // }}}

// 函数定义
func compileFuncDefStmt(context *funcContext, stmt *ast.FuncDefStmt) { // {{{
	if stmt.Name.Func == nil {
		// 对象方法
		reg := context.RegTop()
		var treg, kreg int

		// 先找到对象
		compileExprWithKMVPropagation(context, stmt.Name.Receiver, &reg, &treg)
		// 再将 method 对应的常量值, 加载到栈上
		kreg = loadRk(context, &reg, stmt.Func, LString(stmt.Name.Method))

		// 现在开始处理函数体, reg 对应的变量将来就是函数了
		compileExpr(context, reg, stmt.Func, ecfuncdef)

		// 最后, 将表对象更新
		context.Code.AddABC(OP_SETTABLE, treg, kreg, reg, sline(stmt.Name.Receiver))
	} else {
		// 具名函数, 相当于把一个匿名函数赋值给一个变量
		astmt := &ast.AssignStmt{Lhs: []ast.Expr{stmt.Name.Func}, Rhs: []ast.Expr{stmt.Func}}
		astmt.SetLine(sline(stmt.Func))
		astmt.SetLastLine(eline(stmt.Func))
		compileAssignStmt(context, astmt)
	}
} // }}}

// 这个函数是处理 for x = 1, 6 do print(x) end 这种语句的
func compileNumberForStmt(context *funcContext, stmt *ast.NumberForStmt) { // {{{
	code := context.Code
	endlabel := context.NewLabel()
	ec := &expcontext{}

	// 先定义好代码块, 并且将运行时栈找出来
	context.EnterBlock(endlabel, stmt)
	reg := context.RegTop()

	// 注册变量, 三个特殊变量各自注册(编译过程中可能出现其他变量) + 编译
	rindex := context.RegisterLocalVar("(for index)")
	ecupdate(ec, ecLocal, rindex, 0)
	compileExpr(context, reg, stmt.Init, ec)

	reg = context.RegTop()
	rlimit := context.RegisterLocalVar("(for limit)")
	ecupdate(ec, ecLocal, rlimit, 0)
	compileExpr(context, reg, stmt.Limit, ec)

	// 默认步长是 1
	reg = context.RegTop()
	rstep := context.RegisterLocalVar("(for step)")
	if stmt.Step == nil {
		stmt.Step = &ast.NumberExpr{Value: "1"}
		stmt.Step.SetLine(sline(stmt.Init))
	}
	ecupdate(ec, ecLocal, rstep, 0)
	compileExpr(context, reg, stmt.Step, ec)

	code.AddASbx(OP_FORPREP, rindex, 0, sline(stmt))

	context.RegisterLocalVar(stmt.Name)

	bodypc := code.LastPC()
	compileChunk(context, stmt.Stmts)

	context.LeaveBlock()

	flpc := code.LastPC()
	code.AddASbx(OP_FORLOOP, rindex, bodypc-(flpc+1), sline(stmt))

	context.SetLabelPc(endlabel, code.LastPC())
	code.SetSbx(bodypc, flpc-bodypc)

} // }}}

func compileGenericForStmt(context *funcContext, stmt *ast.GenericForStmt) { // {{{
	code := context.Code
	endlabel := context.NewLabel()
	bodylabel := context.NewLabel()
	fllabel := context.NewLabel()
	nnames := len(stmt.Names)

	context.EnterBlock(endlabel, stmt)
	rgen := context.RegisterLocalVar("(for generator)")
	context.RegisterLocalVar("(for state)")
	context.RegisterLocalVar("(for control)")

	compileRegAssignment(context, stmt.Names, stmt.Exprs, context.RegTop()-3, 3, sline(stmt))

	code.AddASbx(OP_JMP, 0, fllabel, sline(stmt))

	for _, name := range stmt.Names {
		context.RegisterLocalVar(name)
	}

	context.SetLabelPc(bodylabel, code.LastPC())
	compileChunk(context, stmt.Stmts)

	context.LeaveBlock()

	context.SetLabelPc(fllabel, code.LastPC())
	code.AddABC(OP_TFORLOOP, rgen, 0, nnames, sline(stmt))
	code.AddASbx(OP_JMP, 0, bodylabel, sline(stmt))

	context.SetLabelPc(endlabel, code.LastPC())
} // }}}

func compileExpr(context *funcContext, reg int, expr ast.Expr, ec *expcontext) int { // {{{
	code := context.Code
	sreg := savereg(ec, reg)
	sused := 1
	if sreg < reg {
		sused = 0
	}

	switch ex := expr.(type) {
	case *ast.StringExpr:
		code.AddABx(OP_LOADK, sreg, context.ConstIndex(LString(ex.Value)), sline(ex))
		return sused
	case *ast.NumberExpr:
		num, err := parseNumber(ex.Value)
		if err != nil {
			num = LNumber(math.NaN())
		}
		code.AddABx(OP_LOADK, sreg, context.ConstIndex(num), sline(ex))
		return sused
	case *constLValueExpr:
		code.AddABx(OP_LOADK, sreg, context.ConstIndex(ex.Value), sline(ex))
		return sused
	case *ast.NilExpr:
		code.AddLoadNil(sreg, sreg, sline(ex))
		return sused
	case *ast.FalseExpr:
		code.AddABC(OP_LOADBOOL, sreg, 0, 0, sline(ex))
		return sused
	case *ast.TrueExpr:
		code.AddABC(OP_LOADBOOL, sreg, 1, 0, sline(ex))
		return sused
	case *ast.IdentExpr:
		switch getIdentRefType(context, context, ex) {
		case ecGlobal:
			code.AddABx(OP_GETGLOBAL, sreg, context.ConstIndex(LString(ex.Value)), sline(ex))
		case ecUpvalue:
			code.AddABC(OP_GETUPVAL, sreg, context.Upvalues.RegisterUnique(ex.Value), 0, sline(ex))
		case ecLocal:
			b := context.FindLocalVar(ex.Value)
			code.AddABC(OP_MOVE, sreg, b, 0, sline(ex))
		}
		return sused
	case *ast.Comma3Expr:
		if context.Proto.IsVarArg == 0 {
			raiseCompileError(context, sline(ex), "cannot use '...' outside a vararg function")
		}
		context.Proto.IsVarArg &= ^VarArgNeedsArg
		code.AddABC(OP_VARARG, sreg, 2+ec.varargopt, 0, sline(ex))
		if context.RegTop() > (sreg+2+ec.varargopt) || ec.varargopt < -1 {
			return 0
		}
		return (sreg + 1 + ec.varargopt) - reg
	case *ast.AttrGetExpr:
		a := sreg
		b := reg
		compileExprWithMVPropagation(context, ex.Object, &reg, &b)
		c := reg
		compileExprWithKMVPropagation(context, ex.Key, &reg, &c)
		opcode := OP_GETTABLE
		if _, ok := ex.Key.(*ast.StringExpr); ok {
			opcode = OP_GETTABLEKS
		}
		code.AddABC(opcode, a, b, c, sline(ex))
		return sused
	case *ast.TableExpr:
		compileTableExpr(context, reg, ex, ec)
		return 1
	case *ast.ArithmeticOpExpr:
		compileArithmeticOpExpr(context, reg, ex, ec)
		return sused
	case *ast.StringConcatOpExpr:
		compileStringConcatOpExpr(context, reg, ex, ec)
		return sused
	case *ast.UnaryMinusOpExpr, *ast.UnaryNotOpExpr, *ast.UnaryLenOpExpr:
		compileUnaryOpExpr(context, reg, ex, ec)
		return sused
	case *ast.RelationalOpExpr:
		compileRelationalOpExpr(context, reg, ex, ec)
		return sused
	case *ast.LogicalOpExpr:
		compileLogicalOpExpr(context, reg, ex, ec)
		return sused
	case *ast.FuncCallExpr:
		return compileFuncCallExpr(context, reg, ex, ec)
	case *ast.FunctionExpr:
		childcontext := newFuncContext(context.Proto.SourceName, context)
		compileFunctionExpr(childcontext, ex, ec)
		protono := len(context.Proto.FunctionPrototypes)
		context.Proto.FunctionPrototypes = append(context.Proto.FunctionPrototypes, childcontext.Proto)
		code.AddABx(OP_CLOSURE, sreg, protono, sline(ex))
		for _, upvalue := range childcontext.Upvalues.List() {
			localidx, block := context.FindLocalVarAndBlock(upvalue.Name)
			if localidx > -1 {
				code.AddABC(OP_MOVE, 0, localidx, 0, sline(ex))
				block.RefUpvalue = true
			} else {
				upvalueidx := context.Upvalues.Find(upvalue.Name)
				if upvalueidx < 0 {
					upvalueidx = context.Upvalues.RegisterUnique(upvalue.Name)
				}
				code.AddABC(OP_GETUPVAL, 0, upvalueidx, 0, sline(ex))
			}
		}
		return sused
	default:
		panic(fmt.Sprintf("expr %v not implemented.", reflect.TypeOf(ex).Elem().Name()))
	}

} // }}}

func compileExprWithPropagation(context *funcContext, expr ast.Expr, reg *int, save *int, propergator func(int, *int, *int, int)) { // {{{
	reginc := compileExpr(context, *reg, expr, ecnone(0))
	if _, ok := expr.(*ast.LogicalOpExpr); ok {
		*save = *reg
		*reg = *reg + reginc
	} else {
		propergator(context.RegTop(), save, reg, reginc)
	}
} // }}}

func compileExprWithKMVPropagation(context *funcContext, expr ast.Expr, reg *int, save *int) { // {{{
	compileExprWithPropagation(context, expr, reg, save, context.Code.PropagateKMV)
} // }}}

func compileExprWithMVPropagation(context *funcContext, expr ast.Expr, reg *int, save *int) { // {{{
	compileExprWithPropagation(context, expr, reg, save, context.Code.PropagateMV)
} // }}}

func constFold(exp ast.Expr) ast.Expr { // {{{
	switch expr := exp.(type) {
	case *ast.ArithmeticOpExpr:
		lvalue, lisconst := lnumberValue(constFold(expr.Lhs))
		rvalue, risconst := lnumberValue(constFold(expr.Rhs))
		if lisconst && risconst {
			switch expr.Operator {
			case "+":
				return &constLValueExpr{Value: lvalue + rvalue}
			case "-":
				return &constLValueExpr{Value: lvalue - rvalue}
			case "*":
				return &constLValueExpr{Value: lvalue * rvalue}
			case "/":
				return &constLValueExpr{Value: lvalue / rvalue}
			case "%":
				return &constLValueExpr{Value: luaModulo(lvalue, rvalue)}
			case "^":
				return &constLValueExpr{Value: LNumber(math.Pow(float64(lvalue), float64(rvalue)))}
			default:
				panic(fmt.Sprintf("unknown binop: %v", expr.Operator))
			}
		} else {
			return expr
		}
	case *ast.UnaryMinusOpExpr:
		expr.Expr = constFold(expr.Expr)
		if value, ok := lnumberValue(expr.Expr); ok {
			return &constLValueExpr{Value: LNumber(-value)}
		}
		return expr
	default:

		return exp
	}
} // }}}

func compileFunctionExpr(context *funcContext, funcexpr *ast.FunctionExpr, ec *expcontext) { // {{{
	context.Proto.LineDefined = sline(funcexpr)
	context.Proto.LastLineDefined = eline(funcexpr)
	if len(funcexpr.ParList.Names) > maxRegisters {
		raiseCompileError(context, context.Proto.LineDefined, "register overflow")
	}

	context.Proto.NumParameters = uint8(len(funcexpr.ParList.Names))
	if ec.ctype == ecMethod {
		context.Proto.NumParameters += 1
		context.RegisterLocalVar("self")
	}

	// 将变量名字注册到函数的变量符号表里面去
	for _, name := range funcexpr.ParList.Names {
		context.RegisterLocalVar(name)
	}

	if funcexpr.ParList.HasVargs {
		if CompatVarArg {
			// TODO: 这是什么意思?
			context.Proto.IsVarArg = VarArgHasArg | VarArgNeedsArg
			if context.Parent != nil {
				context.RegisterLocalVar("arg")
			}
		}
		context.Proto.IsVarArg |= VarArgIsVarArg
	}

	compileChunk(context, funcexpr.Stmts)

	context.Code.AddABC(OP_RETURN, 0, 1, 0, eline(funcexpr))
	context.EndScope()

	context.Proto.Code = context.Code.List() // 函数编译之后对应的字节码存放在 code 里面
	context.Proto.DbgSourcePositions = context.Code.PosList()
	context.Proto.DbgUpvalues = context.Upvalues.Names()
	context.Proto.NumUpvalues = uint8(len(context.Proto.DbgUpvalues))

	// 遍历函数常量表, 并将字符串常量存在 stringConstants 里面
	for _, clv := range context.Proto.Constants {
		sv := ""
		if slv, ok := clv.(LString); ok {
			sv = string(slv)
		}

		context.Proto.stringConstants = append(context.Proto.stringConstants, sv)
	}

	patchCode(context)
} // }}}

func compileTableExpr(context *funcContext, reg int, ex *ast.TableExpr, ec *expcontext) { // {{{
	code := context.Code
	/*
		tablereg := savereg(ec, reg)
		if tablereg == reg {
			reg += 1
		}
	*/
	tablereg := reg
	reg++
	code.AddABC(OP_NEWTABLE, tablereg, 0, 0, sline(ex))
	tablepc := code.LastPC()
	regbase := reg

	arraycount := 0
	lastvararg := false
	for i, field := range ex.Fields {
		islast := i == len(ex.Fields)-1
		if field.Key == nil {
			if islast && isVarArgReturnExpr(field.Value) {
				reg += compileExpr(context, reg, field.Value, ecnone(-2))
				lastvararg = true
			} else {
				reg += compileExpr(context, reg, field.Value, ecnone(0))
				arraycount += 1
			}
		} else {
			regorg := reg
			b := reg
			compileExprWithKMVPropagation(context, field.Key, &reg, &b)
			c := reg
			compileExprWithKMVPropagation(context, field.Value, &reg, &c)
			opcode := OP_SETTABLE
			if _, ok := field.Key.(*ast.StringExpr); ok {
				opcode = OP_SETTABLEKS
			}
			code.AddABC(opcode, tablereg, b, c, sline(ex))
			reg = regorg
		}
		flush := arraycount % FieldsPerFlush
		if (arraycount != 0 && (flush == 0 || islast)) || lastvararg {
			reg = regbase
			num := flush
			if num == 0 {
				num = FieldsPerFlush
			}
			c := (arraycount-1)/FieldsPerFlush + 1
			b := num
			if islast && isVarArgReturnExpr(field.Value) {
				b = 0
			}
			line := field.Value
			if field.Key != nil {
				line = field.Key
			}
			if c > 511 {
				c = 0
			}
			code.AddABC(OP_SETLIST, tablereg, b, c, sline(line))
			if c == 0 {
				code.Add(uint32(c), sline(line))
			}
		}
	}
	code.SetB(tablepc, int2Fb(arraycount))
	code.SetC(tablepc, int2Fb(len(ex.Fields)-arraycount))
	if shouldmove(ec, tablereg) {
		code.AddABC(OP_MOVE, ec.reg, tablereg, 0, sline(ex))
	}
} // }}}

func compileArithmeticOpExpr(context *funcContext, reg int, expr *ast.ArithmeticOpExpr, ec *expcontext) { // {{{
	exp := constFold(expr)
	if ex, ok := exp.(*constLValueExpr); ok {
		exp.SetLine(sline(expr))
		compileExpr(context, reg, ex, ec)
		return
	}
	expr, _ = exp.(*ast.ArithmeticOpExpr)
	a := savereg(ec, reg)
	b := reg
	compileExprWithKMVPropagation(context, expr.Lhs, &reg, &b)
	c := reg
	compileExprWithKMVPropagation(context, expr.Rhs, &reg, &c)

	op := 0
	switch expr.Operator {
	case "+":
		op = OP_ADD
	case "-":
		op = OP_SUB
	case "*":
		op = OP_MUL
	case "/":
		op = OP_DIV
	case "%":
		op = OP_MOD
	case "^":
		op = OP_POW
	}
	context.Code.AddABC(op, a, b, c, sline(expr))
} // }}}

func compileStringConcatOpExpr(context *funcContext, reg int, expr *ast.StringConcatOpExpr, ec *expcontext) { // {{{
	code := context.Code
	crange := 1
	for current := expr.Rhs; current != nil; {
		if ex, ok := current.(*ast.StringConcatOpExpr); ok {
			crange += 1
			current = ex.Rhs
		} else {
			current = nil
		}
	}
	a := savereg(ec, reg)
	basereg := reg
	reg += compileExpr(context, reg, expr.Lhs, ecnone(0))
	reg += compileExpr(context, reg, expr.Rhs, ecnone(0))
	for pc := code.LastPC(); pc != 0 && opGetOpCode(code.At(pc)) == OP_CONCAT; pc-- {
		code.Pop()
	}
	code.AddABC(OP_CONCAT, a, basereg, basereg+crange, sline(expr))
} // }}}

func compileUnaryOpExpr(context *funcContext, reg int, expr ast.Expr, ec *expcontext) { // {{{
	opcode := 0
	code := context.Code
	var operandexpr ast.Expr
	switch ex := expr.(type) {
	case *ast.UnaryMinusOpExpr:
		exp := constFold(ex)
		if lvexpr, ok := exp.(*constLValueExpr); ok {
			exp.SetLine(sline(expr))
			compileExpr(context, reg, lvexpr, ec)
			return
		}
		ex, _ = exp.(*ast.UnaryMinusOpExpr)
		operandexpr = ex.Expr
		opcode = OP_UNM
	case *ast.UnaryNotOpExpr:
		switch ex.Expr.(type) {
		case *ast.TrueExpr:
			code.AddABC(OP_LOADBOOL, savereg(ec, reg), 0, 0, sline(expr))
			return
		case *ast.FalseExpr, *ast.NilExpr:
			code.AddABC(OP_LOADBOOL, savereg(ec, reg), 1, 0, sline(expr))
			return
		default:
			opcode = OP_NOT
			operandexpr = ex.Expr
		}
	case *ast.UnaryLenOpExpr:
		opcode = OP_LEN
		operandexpr = ex.Expr
	}

	a := savereg(ec, reg)
	b := reg
	compileExprWithMVPropagation(context, operandexpr, &reg, &b)
	code.AddABC(opcode, a, b, 0, sline(expr))
} // }}}

func compileRelationalOpExprAux(context *funcContext, reg int, expr *ast.RelationalOpExpr, flip int, label int) { // {{{
	code := context.Code
	b := reg
	compileExprWithKMVPropagation(context, expr.Lhs, &reg, &b)
	c := reg
	compileExprWithKMVPropagation(context, expr.Rhs, &reg, &c)
	switch expr.Operator {
	case "<":
		code.AddABC(OP_LT, 0^flip, b, c, sline(expr))
	case ">":
		code.AddABC(OP_LT, 0^flip, c, b, sline(expr))
	case "<=":
		code.AddABC(OP_LE, 0^flip, b, c, sline(expr))
	case ">=":
		code.AddABC(OP_LE, 0^flip, c, b, sline(expr))
	case "==":
		code.AddABC(OP_EQ, 0^flip, b, c, sline(expr))
	case "~=":
		code.AddABC(OP_EQ, 1^flip, b, c, sline(expr))
	}
	code.AddASbx(OP_JMP, 0, label, sline(expr))
} // }}}

func compileRelationalOpExpr(context *funcContext, reg int, expr *ast.RelationalOpExpr, ec *expcontext) { // {{{
	a := savereg(ec, reg)
	code := context.Code
	jumplabel := context.NewLabel()
	compileRelationalOpExprAux(context, reg, expr, 1, jumplabel)
	code.AddABC(OP_LOADBOOL, a, 0, 1, sline(expr))
	context.SetLabelPc(jumplabel, code.LastPC())
	code.AddABC(OP_LOADBOOL, a, 1, 0, sline(expr))
} // }}}

func compileLogicalOpExpr(context *funcContext, reg int, expr *ast.LogicalOpExpr, ec *expcontext) { // {{{
	a := savereg(ec, reg)
	code := context.Code
	endlabel := context.NewLabel()
	lb := &lblabels{context.NewLabel(), context.NewLabel(), endlabel, false}
	nextcondlabel := context.NewLabel()
	if expr.Operator == "and" {
		compileLogicalOpExprAux(context, reg, expr.Lhs, ec, nextcondlabel, endlabel, false, lb)
		context.SetLabelPc(nextcondlabel, code.LastPC())
		compileLogicalOpExprAux(context, reg, expr.Rhs, ec, endlabel, endlabel, false, lb)
	} else {
		compileLogicalOpExprAux(context, reg, expr.Lhs, ec, endlabel, nextcondlabel, true, lb)
		context.SetLabelPc(nextcondlabel, code.LastPC())
		compileLogicalOpExprAux(context, reg, expr.Rhs, ec, endlabel, endlabel, false, lb)
	}

	if lb.b {
		context.SetLabelPc(lb.f, code.LastPC())
		code.AddABC(OP_LOADBOOL, a, 0, 1, sline(expr))
		context.SetLabelPc(lb.t, code.LastPC())
		code.AddABC(OP_LOADBOOL, a, 1, 0, sline(expr))
	}

	lastinst := code.Last()
	if opGetOpCode(lastinst) == OP_JMP && opGetArgSbx(lastinst) == endlabel {
		code.Pop()
	}

	context.SetLabelPc(endlabel, code.LastPC())
} // }}}

// {{{
func compileLogicalOpExprAux(context *funcContext, reg int, expr ast.Expr, ec *expcontext, thenlabel, elselabel int, hasnextcond bool, lb *lblabels) {
	// TODO folding constants?
	code := context.Code
	flip := 0
	jumplabel := elselabel
	if hasnextcond {
		flip = 1
		jumplabel = thenlabel
	}

	switch ex := expr.(type) {
	case *ast.FalseExpr:
		if elselabel == lb.e {
			code.AddASbx(OP_JMP, 0, lb.f, sline(expr))
			lb.b = true
		} else {
			code.AddASbx(OP_JMP, 0, elselabel, sline(expr))
		}
		return
	case *ast.NilExpr:
		if elselabel == lb.e {
			compileExpr(context, reg, expr, ec)
			code.AddASbx(OP_JMP, 0, lb.e, sline(expr))
		} else {
			code.AddASbx(OP_JMP, 0, elselabel, sline(expr))
		}
		return
	case *ast.TrueExpr:
		if thenlabel == lb.e {
			code.AddASbx(OP_JMP, 0, lb.t, sline(expr))
			lb.b = true
		} else {
			code.AddASbx(OP_JMP, 0, thenlabel, sline(expr))
		}
		return
	case *ast.NumberExpr, *ast.StringExpr:
		if thenlabel == lb.e {
			compileExpr(context, reg, expr, ec)
			code.AddASbx(OP_JMP, 0, lb.e, sline(expr))
		} else {
			code.AddASbx(OP_JMP, 0, thenlabel, sline(expr))
		}
		return
	case *ast.LogicalOpExpr:
		switch ex.Operator {
		case "and":
			nextcondlabel := context.NewLabel()
			compileLogicalOpExprAux(context, reg, ex.Lhs, ec, nextcondlabel, elselabel, false, lb)
			context.SetLabelPc(nextcondlabel, context.Code.LastPC())
			compileLogicalOpExprAux(context, reg, ex.Rhs, ec, thenlabel, elselabel, hasnextcond, lb)
		case "or":
			nextcondlabel := context.NewLabel()
			compileLogicalOpExprAux(context, reg, ex.Lhs, ec, thenlabel, nextcondlabel, true, lb)
			context.SetLabelPc(nextcondlabel, context.Code.LastPC())
			compileLogicalOpExprAux(context, reg, ex.Rhs, ec, thenlabel, elselabel, hasnextcond, lb)
		}
		return
	case *ast.RelationalOpExpr:
		if thenlabel == elselabel {
			flip ^= 1
			jumplabel = lb.t
			lb.b = true
		} else if thenlabel == lb.e {
			jumplabel = lb.t
			lb.b = true
		} else if elselabel == lb.e {
			jumplabel = lb.f
			lb.b = true
		}
		compileRelationalOpExprAux(context, reg, ex, flip, jumplabel)
		return
	}

	a := reg
	sreg := savereg(ec, a)
	if !hasnextcond && thenlabel == elselabel {
		reg += compileExpr(context, reg, expr, &expcontext{ec.ctype, intMax(a, sreg), ec.varargopt})
		last := context.Code.Last()
		if opGetOpCode(last) == OP_MOVE && opGetArgA(last) == a {
			context.Code.SetA(context.Code.LastPC(), sreg)
		} else {
			context.Code.AddABC(OP_MOVE, sreg, a, 0, sline(expr))
		}
	} else {
		reg += compileExpr(context, reg, expr, ecnone(0))
		if sreg == a {
			code.AddABC(OP_TEST, a, 0, 0^flip, sline(expr))
		} else {
			code.AddABC(OP_TESTSET, sreg, a, 0^flip, sline(expr))
		}
	}
	code.AddASbx(OP_JMP, 0, jumplabel, sline(expr))
} // }}}

func compileFuncCallExpr(context *funcContext, reg int, expr *ast.FuncCallExpr, ec *expcontext) int { // {{{
	funcreg := reg
	if ec.ctype == ecLocal && ec.reg == (int(context.Proto.NumParameters)-1) {
		funcreg = ec.reg
		reg = ec.reg
	}
	argc := len(expr.Args)
	islastvararg := false
	name := "(anonymous)"

	if expr.Func != nil { // hoge.func()
		reg += compileExpr(context, reg, expr.Func, ecnone(0))
		name = getExprName(context, expr.Func)
	} else { // hoge:method()
		b := reg
		compileExprWithMVPropagation(context, expr.Receiver, &reg, &b)
		c := loadRk(context, &reg, expr, LString(expr.Method))
		context.Code.AddABC(OP_SELF, funcreg, b, c, sline(expr))
		// increments a register for an implicit "self"
		reg = b + 1
		reg2 := funcreg + 2
		if reg2 > reg {
			reg = reg2
		}
		argc += 1
		name = string(expr.Method)
	}

	for i, ar := range expr.Args {
		islastvararg = (i == len(expr.Args)-1) && isVarArgReturnExpr(ar)
		if islastvararg {
			compileExpr(context, reg, ar, ecnone(-2))
		} else {
			reg += compileExpr(context, reg, ar, ecnone(0))
		}
	}
	b := argc + 1
	if islastvararg {
		b = 0
	}
	context.Code.AddABC(OP_CALL, funcreg, b, ec.varargopt+2, sline(expr))
	context.Proto.DbgCalls = append(context.Proto.DbgCalls, DbgCall{Pc: context.Code.LastPC(), Name: name})

	if ec.varargopt == 0 && shouldmove(ec, funcreg) {
		context.Code.AddABC(OP_MOVE, ec.reg, funcreg, 0, sline(expr))
		return 1
	}
	if context.RegTop() > (funcreg+2+ec.varargopt) || ec.varargopt < -1 {
		return 0
	}
	return ec.varargopt + 1
} // }}}

// 编译 OP_LOADK 指令
func loadRk(context *funcContext, reg *int, expr ast.Expr, cnst LValue) int { // {{{
	cindex := context.ConstIndex(cnst) // 先找到 cnst 对应的常量表索引
	if cindex <= opMaxIndexRk {
		// 如果寄存器空间能放得下 cindex, 则直接使用寄存器空间存放
		return opRkAsk(cindex)
	} else {
		// 寄存器空间放不下, 则生成一条有具体操作数的 OP_LOADK 指令
		// 这条指令在运行时, 将 cindex 位置的常量值, 加载到 ret 对应的位置处
		ret := *reg
		*reg++
		context.Code.AddABx(OP_LOADK, ret, cindex, sline(expr))
		return ret
	}
} // }}}

// 找到变量所属的范围
// 1. 首先看是否是全局变量
// 2. 找本地变量
// 3. 找父函数的本地变量
func getIdentRefType(context *funcContext, current *funcContext, expr *ast.IdentExpr) expContextType { // {{{
	if current == nil {
		return ecGlobal // 全局环境
	} else if current.FindLocalVar(expr.Value) > -1 {
		if current == context {
			return ecLocal
		}

		// 局部变量, 父级块(context != current)的情况下, 就是闭包里面的 upvalue
		return ecUpvalue
	}

	return getIdentRefType(context, current.Parent, expr)
} // }}}

func getExprName(context *funcContext, expr ast.Expr) string { // {{{
	switch ex := expr.(type) {
	case *ast.IdentExpr:
		return ex.Value
	case *ast.AttrGetExpr:
		switch kex := ex.Key.(type) {
		case *ast.StringExpr:
			return kex.Value
		}
		return "?"
	}
	return "?"
} // }}}

func patchCode(context *funcContext) { // {{{
	maxreg := 1
	if np := int(context.Proto.NumParameters); np > 1 {
		maxreg = np
	}
	moven := 0
	code := context.Code.List()
	for pc := 0; pc < len(code); pc++ {
		inst := code[pc]
		curop := opGetOpCode(inst)
		switch curop {
		case OP_CLOSURE:
			pc += int(context.Proto.FunctionPrototypes[opGetArgBx(inst)].NumUpvalues)
			moven = 0
			continue
		case OP_SETGLOBAL, OP_SETUPVAL, OP_EQ, OP_LT, OP_LE, OP_TEST,
			OP_TAILCALL, OP_RETURN, OP_FORPREP, OP_FORLOOP, OP_TFORLOOP,
			OP_SETLIST, OP_CLOSE:
			/* nothing to do */
		case OP_CALL:
			if reg := opGetArgA(inst) + opGetArgC(inst) - 2; reg > maxreg {
				maxreg = reg
			}
		case OP_VARARG:
			if reg := opGetArgA(inst) + opGetArgB(inst) - 1; reg > maxreg {
				maxreg = reg
			}
		case OP_SELF:
			if reg := opGetArgA(inst) + 1; reg > maxreg {
				maxreg = reg
			}
		case OP_LOADNIL:
			if reg := opGetArgB(inst); reg > maxreg {
				maxreg = reg
			}
		case OP_JMP: // jump to jump optimization
			distance := 0
			count := 0 // avoiding infinite loops
			for jmp := inst; opGetOpCode(jmp) == OP_JMP && count < 5; jmp = context.Code.At(pc + distance + 1) {
				d := context.GetLabelPc(opGetArgSbx(jmp)) - pc
				if d > opMaxArgSbx {
					if distance == 0 {
						raiseCompileError(context, context.Proto.LineDefined, "too long to jump.")
					}
					break
				}
				distance = d
				count++
			}
			if distance == 0 {
				context.Code.SetOpCode(pc, OP_NOP)
			} else {
				context.Code.SetSbx(pc, distance)
			}
		default:
			if reg := opGetArgA(inst); reg > maxreg {
				maxreg = reg
			}
		}

		// bulk move optimization(reducing op dipatch costs)
		if curop == OP_MOVE {
			moven++
		} else {
			if moven > 1 {
				context.Code.SetOpCode(pc-moven, OP_MOVEN)
				context.Code.SetC(pc-moven, intMin(moven-1, opMaxArgsC))
			}
			moven = 0
		}
	}
	maxreg++
	if maxreg > maxRegisters {
		raiseCompileError(context, context.Proto.LineDefined, "register overflow(too many local variables)")
	}
	context.Proto.NumUsedRegisters = uint8(maxreg)
} // }}}

// 这个函数将 ast.Stmt 列表(表示一系列语句) 封装成一个虚拟机可以处理的函数
func Compile(chunk []ast.Stmt, name string) (proto *FunctionProto, err error) { // {{{
	defer func() {
		if rcv := recover(); rcv != nil {
			if _, ok := rcv.(*CompileError); ok {
				err = rcv.(error)
			} else {
				panic(rcv)
			}
		}
	}()

	err = nil
	parlist := &ast.ParList{HasVargs: true, Names: []string{}} // TODO: 这里为啥要设置成有参数呢?
	funcexpr := &ast.FunctionExpr{ParList: parlist, Stmts: chunk}
	context := newFuncContext(name, nil)
	compileFunctionExpr(context, funcexpr, ecnone(0))
	proto = context.Proto
	return
} // }}}
