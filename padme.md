---

---

# Padme Application

A synchronization example of the Lead, Task, Evaluation and Comment concepts.

```alloy
module padme

open fwk/fwk
open task[User, univ]
open evaluation[User]
open lead[Asset, Brief, univ]
open comment[AssessmentBlock] as assessmentCmt
open comment[assessmentCmt/Comment]  as assessmentCmtReply
open comment[QuestionBlock] as questionCmt
open comment[questionCmt/Comment]  as questionCmtReply
```
## Synchronization

```alloy
// Other objects...
var sig User {}
var sig Asset {}
var sig Brief {}

private let removedEvaluations[led] = {e: Evaluation | led.removeItems[e]}
private let removedTasks[led] = {e: Task | led.removeItems[e]}
private let addedEvaluations[led] = {e: Evaluation' | led.addItems[e]}
private let addedTasks[led] = {e: Task' | led.addItems[e]}

/**
* Evaluation <--> Lead
*/

pred removeFromLeadImpliesDeleteEval {
	all led: Lead | all rem: led.removedEvaluations | rem.delete
}

/**
* Evaluation <--> Task
*/

pred finishEvalEquivCompleteTask {
	// TODO
}

pred unfinishEvalEquivReopenTask {
	// TODO
}

/**
* Task <--> Lead
*/

pred removeFromLeadImpliesDeleteTask {
	all led: Lead | all rem: led.removedTasks | rem.delete
}

/**
* Evaluation <--> Task <--> Lead
*/

pred addEvalToLeadEquivAddRelatedTaskToLead {
	all led: Lead {
		all evl: led.addedEvaluations {
			one tsk: Task' | tsk.taskObject' = evl and led.addItems[tsk] and after (led.stageOf[evl] = led.stageOf[tsk])
		}
		all tsk: led.addedTasks | let evl = tsk.taskObject' {
			(some evl and evl in Evaluation') implies (led.addItems[evl] and after (led.stageOf[evl] = led.stageOf[tsk]))
		}
	}
}

pred removeEvalFromLeadImpliesRemoveRelatedTasksFromLead {
	all led: Lead {
		all evl: led.removedEvaluations {
			all tsk: taskObject.evl | led.removeItems[tsk]
		}
	}
}

fact{
	always {
		removeFromLeadImpliesDeleteEval
		removeFromLeadImpliesDeleteTask
		addEvalToLeadEquivAddRelatedTaskToLead
		removeEvalFromLeadImpliesRemoveRelatedTasksFromLead
	}
}
```
## Invariants

```alloy
fact{
	always {
		Task.taskObject in Evaluation
		Lead.findAllItems in (Task + Evaluation)
	}
}
```

## Visualization

```alloy
fun events: univ -> univ {
	taskEvents 
	+ evaluationEvents 
	+ leadEvents 
	+ assessmentCmt/commentEvents
	+ assessmentCmtReply/commentEvents
	+ questionCmt/commentEvents
	+ questionCmtReply/commentEvents
}
```
## Simulation

```alloy
run simulation {
	always #events <= 3
	no Task 
	no Evaluation
	no Lead
	eventually some led: Lead, evl: Evaluation' | led.addItems[evl]
}
```
