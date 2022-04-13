---

---

# Padme Application

A synchronization example of the Lead, Task, Evaluation and Comment concepts.

```alloy
module padme

open fwk/fwk
open task[User, Evaluation, Evaluation, Evaluation]
open evaluation[User]
open lead[Asset, Brief, Evaluation, Task, Task]
open comment[Comment, QuestionBlock, AssessmentBlock]
```
## Synchronization

```alloy
// Other objects...
var sig User {}
var sig Asset {}
var sig Brief {}


/**
* Evaluation <--> Lead
*/

pred removeFromLeadImpliesDeleteEval {
	all led: Lead | all eval: Evaluation {
		(eval in led.findAllItems and after (eval not in led.findAllItems)) implies eval.delete
	} 
}

/**
* Evaluation <--> Task
*/

pred finishEvalEquivCompleteTask {
	
}

pred unfinishEvalEquivReopenTask {
	
}

/**
* Task <--> Lead
*/

pred removeFromLeadImpliesDeleteTask {
	all led: Lead | all tsk: Task {
		(tsk in led.findAllItems and after (tsk not in led.findAllItems)) implies tsk.delete
	} 
}

/**
* Evaluation <--> Task <--> Lead
*/

pred addEvalToLeadEquivAddRelatedTaskToLead {
	all led: Lead | all evl: Evaluation' {
		(evl not in led.findItems and after (evl in led.findItems)) implies after one tsk: Task {
			tsk.taskObject = evl
			led.addItems[tsk]
		}

		(evl not in led.findStageItems and after (evl in led.findStageItems)) implies after one tsk: Task {
			tsk.taskObject = evl
			led.addStageItems[led.stageOf[evl], tsk]
		}
	}

	all led: Lead | all tsk: Task' {
		(some tsk.taskObject and (tsk not in led.findItems) and after (tsk in led.findItems)) implies after led.addItems[tsk.taskObject]

		(some tsk.taskObject and (tsk not in led.findStageItems) and after (tsk in led.findStageItems)) implies after led.addStageItems[led.stageOf[tsk], tsk.taskObject]
	}
}

pred removeEvalFromLeadImpliesRemoveRelatedTasksFromLead {
	all led: Lead | all evl: Evaluation {
		(evl in led.findAllItems and after (evl not in led.findAllItems)) implies all tsk: taskObject.evl | led.removeItems[tsk]
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

## Visualization

```alloy
fun events: univ {
	eventAgrs.univ
}

fun eventAgrs: univ -> univ {
	vizTaskEventArgs 
	+ vizEvaluationEventArgs 
	+ vizLeadEventArgs 
	+ vizCommentEventArgs
}
```
## Simulation

```alloy
run simulation {
	always #events <= 3
	no Task 
	no Evaluation
	no Lead
	eventually some Evaluation<:Lead.findAllItems
}
```
