---

---

# Comment

A comment allows to share some thouths about something.

```alloy
module comment[Commentable1, Commentable2, Commentable3]

open fwk/fwk
```

## State

```alloy
private let Commentable = Comment + Commentable1 + Commentable2 + Commentable3

var sig Comment {
	var target: one Commentable,
	var content: one Text,
	var modified: one Boolean
}
```

## Actions

```alloy
pred Comment.createComment[cnt: Text, tgt: Commentable] {
	this.create

	this.target = tgt
	this.content = cnt
}

fun createComment: Comment {
	{c: Comment | c.create}
}

pred Comment.editContent[cnt: Text] {
	this.update[Comment<:content, cnt]
}

fun editContent: set Comment {
	{c: Comment, txt: Text | c.editContent[txt]}.Text
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

pred cannotCommentItself {
	no cmt: Comment | cmt.target = cmt
}

pred oneLevelReply {
	no cmt: Comment | some cmt.target.target and cmt.target.target in Comment
}

pred syncModifiedFlagAndEdit {
	all cmt: Comment {
		cmt.modified != cmt.modified' <=> cmt in editContent
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
		cannotCommentItself
		oneLevelReply
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
	CreateComment,
	EditContentComment
}

fun vizCommentEvents: set CommentEvent {
	vizCommentEventArgs.Comment
}

fun vizCommentEventArgs: CommentEvent -> Comment {
	CreateComment -> createComment +
	EditContentComment -> editContent
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
	eventually some createComment
}

pred commentAndEditPrinciple {
	eventually some editContent
}

check goodStateOfNotEdited 
check goodStateOfEdited 
run commentPrinciple
run commentAndEditPrinciple
```
