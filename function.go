package lua

import (
	"fmt"
	"strings"
)

const (
	VarArgHasArg   uint8 = 1
	VarArgIsVarArg uint8 = 2
	VarArgNeedsArg uint8 = 4
)

// DbgLocalInfo 结构用于记录本地变量的调试信息
type DbgLocalInfo struct {
	Name    string // 变量名称
	StartPc int    // 变量作用域开始 pc 位置
	EndPc   int    // 变量作用域失效 pc 位置
}

type DbgCall struct {
	Name string
	Pc   int
}

type FunctionProto struct {
	SourceName         string // 函数名
	LineDefined        int    // 函数定义开始行
	LastLineDefined    int    // 函数定义结束行
	NumUpvalues        uint8  // TODO: what is upvalues?
	NumParameters      uint8  // 函数参数数量
	IsVarArg           uint8
	NumUsedRegisters   uint8 // 使用寄存器的数量
	Code               []uint32
	Constants          []LValue // 函数中使用到的 lua 常量
	FunctionPrototypes []*FunctionProto

	DbgSourcePositions []int           // 函数代码所在的行号
	DbgLocals          []*DbgLocalInfo // 本地变量 debug 相关
	DbgCalls           []DbgCall
	DbgUpvalues        []string

	stringConstants []string // 函数中使用的字符串常量
}

/* Upvalue {{{ */

type Upvalue struct {
	next   *Upvalue
	reg    *registry
	index  int
	value  LValue
	closed bool
}

func (uv *Upvalue) Value() LValue {
	//if uv.IsClosed() {
	if uv.closed || uv.reg == nil {
		return uv.value
	}
	//return uv.reg.Get(uv.index)
	return uv.reg.array[uv.index]
}

func (uv *Upvalue) SetValue(value LValue) {
	if uv.IsClosed() {
		uv.value = value
	} else {
		uv.reg.Set(uv.index, value)
	}
}

func (uv *Upvalue) Close() {
	value := uv.Value()
	uv.closed = true
	uv.value = value
}

func (uv *Upvalue) IsClosed() bool {
	return uv.closed || uv.reg == nil
}

func UpvalueIndex(i int) int {
	return GlobalsIndex - i
}

/* }}} */

/* FunctionProto {{{ */

func newFunctionProto(name string) *FunctionProto {
	return &FunctionProto{
		SourceName:         name,
		LineDefined:        0,
		LastLineDefined:    0,
		NumUpvalues:        0,
		NumParameters:      0,
		IsVarArg:           0,
		NumUsedRegisters:   2,
		Code:               make([]uint32, 0, 128),
		Constants:          make([]LValue, 0, 32),
		FunctionPrototypes: make([]*FunctionProto, 0, 16),

		DbgSourcePositions: make([]int, 0, 128),
		DbgLocals:          make([]*DbgLocalInfo, 0, 16),
		DbgCalls:           make([]DbgCall, 0, 128),
		DbgUpvalues:        make([]string, 0, 16),

		stringConstants: make([]string, 0, 32),
	}
}

func (fp *FunctionProto) String() string {
	return fp.str(1, 0)
}

func (fp *FunctionProto) str(level int, count int) string {
	indent := strings.Repeat("  ", level-1)
	buf := []string{}
	buf = append(buf, fmt.Sprintf("%v; function [%v] definition (level %v)\n",
		indent, count, level))
	buf = append(buf, fmt.Sprintf("%v; %v upvalues, %v params, %v stacks\n",
		indent, fp.NumUpvalues, fp.NumParameters, fp.NumUsedRegisters))
	for reg, linfo := range fp.DbgLocals {
		buf = append(buf, fmt.Sprintf("%v.local %v ; %v\n", indent, linfo.Name, reg))
	}
	for reg, upvalue := range fp.DbgUpvalues {
		buf = append(buf, fmt.Sprintf("%v.upvalue %v ; %v\n", indent, upvalue, reg))
	}
	for reg, conzt := range fp.Constants {
		buf = append(buf, fmt.Sprintf("%v.const %v ; %v\n", indent, conzt.String(), reg))
	}
	buf = append(buf, "\n")

	protono := 0
	for no, code := range fp.Code {
		inst := opGetOpCode(code)
		if inst == OP_CLOSURE {
			buf = append(buf, "\n")
			buf = append(buf, fp.FunctionPrototypes[protono].str(level+1, protono))
			buf = append(buf, "\n")
			protono++
		}
		buf = append(buf, fmt.Sprintf("%v[%03d] %v (line:%v)\n",
			indent, no+1, opToString(code), fp.DbgSourcePositions[no]))

	}
	buf = append(buf, fmt.Sprintf("%v; end of function\n", indent))
	return strings.Join(buf, "")
}

/* }}} */

/* LFunction {{{ */

func newLFunctionL(proto *FunctionProto, env *LTable, nupvalue int) *LFunction {
	return &LFunction{
		IsG: false,
		Env: env,

		Proto:     proto,
		GFunction: nil,
		Upvalues:  make([]*Upvalue, nupvalue),
	}
}

func newLFunctionG(gfunc LGFunction, env *LTable, nupvalue int) *LFunction {
	return &LFunction{
		IsG: true,
		Env: env,

		Proto:     nil,
		GFunction: gfunc,
		Upvalues:  make([]*Upvalue, nupvalue),
	}
}

func (fn *LFunction) LocalName(regno, pc int) (string, bool) {
	if fn.IsG {
		return "", false
	}
	p := fn.Proto
	for i := 0; i < len(p.DbgLocals) && p.DbgLocals[i].StartPc < pc; i++ {
		if pc < p.DbgLocals[i].EndPc {
			regno--
			if regno == 0 {
				return p.DbgLocals[i].Name, true
			}
		}
	}
	return "", false
}

/* }}} */
