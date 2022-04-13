---

---

```alloy
module fwk/ordered_value[Value0, Value1, Value2]

private let Value = (Value0 + Value1 + Value2)

pred isBefore[a, b: Value] {
	some a 
	some b 
	a in beforeOf[b]
}

pred isAfter[a, b: Value] {
	some a 
	some b
	a in afterOf[b]
}

fun beforeOf[v: Value]: set Value {
	v.^{a, b: Value | b = justBeforeOf[a]}
}

fun justBeforeOf[a: Value]: lone Value {
	a = Value2 implies Value1
	else a = Value1 implies Value0
	else none
}

fun afterOf[v: Value]: set Value {
	v.^{a, b: Value | b = justAfterOf[a]}
}

fun justAfterOf[a: Value]: lone Value {
	a = Value0 implies Value1
	else a = Value1 implies Value2
	else none
}

run {} for 1
```