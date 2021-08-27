package ast

type Field struct {
	Key   Expr
	Value Expr
}

type ParList struct {
	HasVargs bool     // 生成的函数是否有参数
	Names    []string // 以及参数的名字
}

type FuncName struct {
	Func Expr //具名函数名称

	// 下面是匿名函数, 或者对象方法
	Receiver Expr
	Method   string
}
