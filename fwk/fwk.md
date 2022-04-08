---

---

```alloy
module fwk/fwk

open fwk/boolean
open fwk/text
open fwk/date

// Trick for first step
pred isFirstStep {
	not before isTrue[True] 
}

// Existance
pred exist[u: univ] {
	some u and u in univ
}

pred notExist[u: univ] {
	u not in univ
}

pred existBefore[u: univ] {
	before u.exist
}

pred notExistBefore[u: univ] {
	(before u.notExist) or isFirstStep
}

pred existAfter[u: univ] {
	after u.exist
}

pred notExistAfter[u: univ] {
	after u.notExist
}

// Repository Actions
pred create[u: univ] {
	u.notExist and u.existAfter
}

pred created[u: univ] {
	(before u.create) or (isFirstStep and u.exist)
}

pred delete[u: univ] {
	u.exist and u.notExistAfter
}

pred canUpdate[u: univ] {
	u.exist and u.existAfter
}

pred update[obj: univ, rel: univ -> univ] {
	some obj
	all o: obj {
		o.update[rel, none] or some val: univ | o.update[rel, val]
	}
}

pred update[obj: univ, rel: univ -> univ, val: univ] {
	obj.canUpdate
	all o: obj | o.rel != val and o.rel' = val
}

pred updateByAdding[obj: univ, rel: univ -> univ] {
	some obj
	all o: obj {
		some val: univ | o.updateByAdding[rel, val]
	}
}

pred updateByAdding[obj: univ, rel: univ -> univ, val: univ] {
	some val
	obj.canUpdate
	all o: obj | val not in o.rel and val in o.rel'
}

pred updateByRemoving[obj: univ, rel: univ -> univ] {
	some obj
	all o: obj {
		some val: univ | o.updateByRemoving[rel, val]
	}
}

pred updateByRemoving[obj: some univ, rel: univ -> univ, val: univ] {
	some val
	obj.canUpdate
	all o: obj | val in o.rel and val not in o.rel'
}

// Read Only
pred readOnly[entity: univ, rel: univ -> univ] {
	entity.canUpdate implies entity.rel = entity.rel'
}

pred readOnly[entity: univ, rel: univ -> univ -> univ] {
	entity.canUpdate implies entity.rel = entity.rel'
}
```