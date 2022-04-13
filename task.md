---

---

# Task

A task allows the assignee to follow up on a job that needs to be done about an object.

```alloy
module task[Assignee, TaskObject1, TaskObject2, TaskObject3]

open fwk/fwk
```

## State

```alloy
private let TaskObject = TaskObject1 + TaskObject2 + TaskObject3

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
pred Task.createTask[tso: TaskObject] {
	this.create

	this.taskObject = tso
}

fun createTask: set Task {
	{t: Task | t.create}
}

fun deleteTask: set Task {
	{t: Task | t.delete}
}

pred Task.editLabel[val: Text] {
	this.update[Task<:label, val]
}

fun editLabel: set Task {
	{t: Task, txt: Text | t.editLabel[txt]}.Text
}

pred Task.editDescription[val: Text] {
	this.update[Task<:description, val]
}

fun editDescription: set Task {
	{t: Task, txt: Text | t.editDescription[txt]}.Text + {t: Task | t.editDescription[none]}
}

pred Task.changeDueDate[val: Date] {
	this.update[Task<:dueDate, val]
}

fun changeDueDate: set Task {
	{t: Task, dte: Date | t.changeDueDate[dte]}.Date + {t: Task | t.changeDueDate[none]}
}

pred Task.assign[val: Assignee] {
	this.update[Task<:assignee, val]
}

fun assign: set Task {
	{t: Task, ase: Assignee | t.assign[ase]}.Assignee + {t: Task | t.assign[none]}
}

pred Task.complete[val: Date] {
	no this.completionDate
	
	this.update[Task<:completionDate, val]
	some this.completionDate'
}

fun complete: set Task {
	{t: Task, dte: Date | t.complete[dte]}.Date
}

pred Task.reopen {
	some this.completionDate

	this.update[Task<:completionDate, none]
	no this.completionDate'
}

fun reopen: set Task {
	{t: Task | t.reopen}
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
	CreateTask, 
	DeleteTask, 
	EditLabelTask, 
	EditDescriptionTask, 
	ChangeDueDateTask, 
	AssignTask, 
	CompleteTask, 
	ReopenTask
}

fun vizTaskEvents: set TaskEvent {
	vizTaskEventArgs.Task
}

fun vizTaskEventArgs: TaskEvent -> Task {
	CreateTask -> createTask +
	DeleteTask -> deleteTask +
	EditLabelTask -> editLabel +
	EditDescriptionTask -> editDescription +
	ChangeDueDateTask -> changeDueDate +
	AssignTask -> assign +
	CompleteTask -> complete +
	ReopenTask -> reopen
}
```

## Simulations

```alloy
pred completeTaskPrinciple {
	eventually some complete
}

run completeTaskPrinciple
```
