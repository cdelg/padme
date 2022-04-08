---

---

```alloy
module fwk/text

enum Text {Text0, Text1, Text2}

pred isEmpty[t: Text] {
	t = Text2
}
```