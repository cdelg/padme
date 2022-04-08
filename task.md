---

---

# Task

A task allows the assignee to follow up on a job that needs to be done about an object.

```alloy
module task[Assignee, TaskObject]

open fwk/fwk
```

## State

```alloy
enum TaskStatus {ActiveTaskStatus, CompletedTaskStatus}

var sig Task {
	var taskObject: lone TaskObject,
	var assignee: lone Assignee,
	var label: one Text,
	var description: lone Text,
	var status: one TaskStatus,
	var dueDate: lone Date,
	var completionDate: lone Date
}
```

## Actions

```alloy
pred editLabel[obj: Task] {
	obj.update[Task<:label]
}

pred editLabel[obj: Task, val: Text] {
	obj.update[Task<:label, val]
}

pred editDescription[obj: Task] {
	obj.update[Task<:description]
}

pred editDescription[obj: Task, val: Text] {
	obj.update[Task<:description, val]
}

pred changeDueDate[obj: Task] {
	obj.update[Task<:dueDate]
}

pred changeDueDate[obj: Task, val: Date] {
	obj.update[Task<:dueDate, val]
}

pred assign[obj: Task] {
	obj.update[Task<:assignee]
}

pred assign[obj: Task, val: Assignee] {
	obj.update[Task<:assignee, val]
}

pred complete[obj: Task] {
	obj.update[Task<:completionDate] and no obj.completionDate and some obj.completionDate'
}

pred complete[obj: Task, val: some Date] {
	obj.update[Task<:completionDate, val] and no obj.completionDate
}

pred reopen[obj: Task] {
	obj.update[Task<:completionDate] and some obj.completionDate and no obj.completionDate'
}
```

## Invariants

```alloy
pred cannotChangeTaskObject {
	Task.readOnly[Task<:taskObject]
}

pred cannotChangeCompletionDate {
	no obj: Task { 	
		some obj.completionDate
		obj.completionDate' != none
		obj.completionDate != obj.completionDate'
	}
}

pred syncStatusWithCompletionDate {
	all obj: Task | no obj.completionDate => obj.status = ActiveTaskStatus else obj.status = CompletedTaskStatus
}

fact{
	always {
		cannotChangeTaskObject
		cannotChangeCompletionDate
		syncStatusWithCompletionDate
	}
}
```

## Visualization

```alloy
enum TaskEvent{
	CreatedTask, 
	DeletedTask, 
	EditedLabelTask, 
	EditedDescriptionTask, 
	ChangedDueDateTask, 
	AssignedTask, 
	CompletedTask, 
	ReopenedTask
}

fun taskEvents: univ -> univ {
	CreatedTask -> {t: Task | t.created}
	+ DeletedTask -> {t: Task |  t.delete}
	+ EditedLabelTask -> {t: Task | before t.editLabel}
	+ EditedDescriptionTask -> {t: Task | before t.editDescription}
	+ ChangedDueDateTask -> {t: Task | before t.changeDueDate}
	+ AssignedTask -> {t: Task | before t.assign}
	+ CompletedTask -> {t: Task | before t.complete}
	+ ReopenedTask -> {t: Task |before t.reopen}
}
```

## Simulations

```alloy
pred completeTaskPrinciple {
	eventually some tsk: Task | tsk.complete
}

run completeTaskPrinciple
```
