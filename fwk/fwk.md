---

---

```alloy
module fwk/fwk

open fwk/boolean
open fwk/text
open fwk/date

// Repository Actions
pred create[u: univ] {
	some u
	not (before u in univ)
	u in univ
}

pred delete[u: univ] {
	some u
	u in univ
	after u not in univ
}

pred canUpdate[u: univ] {
	some u
	u in univ
	after u in univ
}

pred update[obj: univ, rel: univ -> univ, val: univ] {
	obj.canUpdate
	all o: obj | o.rel != val and o.rel' = val
}

pred updateByAdding[obj: univ, rel: univ -> univ, val: univ] {
	some val
	obj.canUpdate
	all o: obj | val not in o.rel and val in o.rel'
}

pred updateByRemoving[obj: some univ, rel: univ -> univ, val: univ] {
	some val
	obj.canUpdate
	all o: obj | val in o.rel and val not in o.rel'
}

// Read Only
pred readOnly[obj: univ, rel: univ -> univ] {
	all o: obj | o.canUpdate implies o.rel = o.rel'
}

pred readOnly[obj: univ, rel: univ -> univ -> univ] {
	all o: obj | o.canUpdate implies o.rel = o.rel'
}
```