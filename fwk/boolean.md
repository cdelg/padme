---

---

```alloy
module fwk/boolean

enum Boolean {True, False}

pred isTrue[p: Boolean] {
	p = True
}

pred isFalse[p: Boolean] {
	not isTrue[p]
}
```