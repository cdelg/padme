---

---

# Comment

A comment allows to share some thouths about something.

```alloy
module comment[Target]

open fwk/fwk
```

## State

```alloy
var sig Comment {
	var target: one Target,
	var content: one Text,
	var modified: one Boolean
}
```

## Actions

```alloy
pred Comment.editContent {
	this.update[Comment<:content]
}

pred Comment.editContent[cnt: Text] {
	this.update[Comment<:content, cnt]
}
```

## Invariants

```alloy
pred cannotChangeCommentTarget {
	Comment.readOnly[Comment<:target] 
}

pred modifiedFlagCanOnlyChangeToTrue {
	no cmt: Comment {
		cmt.modified = True and cmt.modified' = False
	} 
}

pred syncModifiedFlagAndEdit {
	all cmt: Comment {
		cmt.modified != cmt.modified' <=> cmt.editContent
	}
}

pred modifiedFlagFalseByDefault {
	all cmt: Comment {
		once cmt.modified = False
	}
}

pred neverDelete {
	no cmt: Comment {
		cmt.delete
	}
}

fact{
	always {
		cannotChangeCommentTarget
		modifiedFlagCanOnlyChangeToTrue
		syncModifiedFlagAndEdit
		modifiedFlagFalseByDefault
		neverDelete
	}
}
```

## Visualization


```alloy
enum CommentEvent{
	CreatedComment,
	EditedContentComment
}

fun commentEvents: univ -> univ {
	CreatedComment -> {e: Comment| e.created}
	+ EditedContentComment -> {e:  Comment | before e.editContent}
}
```

## Simulations

```alloy
assert goodStateOfNotEdited {
	always all cmt: Comment {
		cmt.modified' = False implies  (no txt: Text | cmt.editContent[txt]) since cmt in univ 
	}
}

assert goodStateOfEdited {
	always all cmt: Comment {
		(some txt: Text | cmt.editContent[txt]) => always cmt.modified' = True
	}
}

pred commentPrinciple {
	eventually some Comment
}

pred commentAndEditPrinciple {
	eventually {
		some Comment 
		eventually some EditedContentComment.commentEvents
	}
}

check goodStateOfNotEdited 
check goodStateOfEdited 
run commentPrinciple
run commentAndEditPrinciple
```
