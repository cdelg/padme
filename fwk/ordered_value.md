---

---

```alloy
module fwk/ordered_value[Value0, Value1, Value2]

private let Value = (Value0 + Value1 + Value2)

pred isBefore[a, b: Value] {
	(a = Value0 and b = Value1)
	or (a = Value0 and b = Value2)
	or (a = Value1 and b = Value2)
}

pred isAfter[a, b: Value] {
	a != b and not isBefore[a, b] 
}

fun beforeOf[a: Value]: set Value {
	{b: Value | b.isBefore[a]}
}

fun afterOf[a: Value]: set Value {
	{b: Value | b.isAfter[a]}
}

run {} for 1
```