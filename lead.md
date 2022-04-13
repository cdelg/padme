---

---

# Lead

A lead allows you to review an asset against a goal by following a workflow.

```alloy
module lead[Asset, Goal, ReviewItem1, ReviewItem2, ReviewItem3]

open fwk/fwk
open fwk/ordered_value[LeadStage1, LeadStage2, LeadStage3]
```

## State

```alloy
private let ReviewItem = ReviewItem1 + ReviewItem2 + ReviewItem3

enum LeadStatus {ActiveLeadStatus, AcceptedLeadStatus, DeclinedLeadStatus}
enum LeadStage {LeadStage1, LeadStage2, LeadStage3}

var sig Lead {
	var asset: one Asset,
	var goal: one Goal,
	var status: one LeadStatus,
	var stage: one LeadStage,
	var leadItems: set ReviewItem,
	var stageItems: LeadStage lone -> ReviewItem,
	var blockers: set ReviewItem
}
```

## Actions

```alloy
fun createLead: set Lead {
	{l: Lead | l.create}
}

fun deleteLead: set Lead {
	{l: Lead | l.delete}
}

pred Lead.accept {
	this.update[Lead<:status, AcceptedLeadStatus]
}

fun accept: set Lead {
	{l: Lead | l.accept}
}

pred Lead.decline {
	this.update[Lead<:status, DeclinedLeadStatus]
}

fun decline: set Lead {
	{l: Lead | l.decline}
}

pred Lead.reopen {
	this.update[Lead<:status, ActiveLeadStatus]
}

fun reopen: set Lead {
	{l: Lead | l.reopen}
}

pred Lead.nextStage {
	this.update[Lead<:stage, justAfterOf[this.stage]]
}

fun nextStage: set Lead {
	{l: Lead | l.nextStage}
}

pred Lead.previousStage {
	this.update[Lead<:stage, justBeforeOf[this.stage]]
}

fun previousStage: set Lead {
	{l: Lead | l.previousStage}
}

pred Lead.addItems[val: ReviewItem] {
	this.updateByAdding[Lead<:leadItems, val]
}

fun addItems: set Lead {
	{l: Lead,  val: ReviewItem| l.addItems[val]}.ReviewItem
}

pred Lead.addStageItems[stg: LeadStage, val: ReviewItem] {
	this.canUpdate
	some stg
	some val

	all o: this | val not in o.stageItems[stg] and val in o.stageItems'[stg]	
}

fun addStageItems: set Lead {
	{l: Lead, stg: LeadStage, val: ReviewItem| l.addStageItems[stg, val]}.ReviewItem.LeadStage
}

pred Lead.removeItems[val: ReviewItem] {
	this.updateByRemoving[Lead<:leadItems, val]
}

fun removeItems: set Lead {
	{l: Lead,  val: ReviewItem| l.removeItems[val]}.ReviewItem
}

pred Lead.removeStageItems[stg: LeadStage, val: ReviewItem] {
	this.canUpdate
	some val
	some stg
	
	all o: this | val in o.stageItems[stg] and val not in o.stageItems'[stg]
}

fun removeStageItems: set Lead {
	{l: Lead, stg: LeadStage, val: ReviewItem| l.removeStageItems[stg, val]}.ReviewItem.LeadStage
}

pred Lead.addBlockingMark[val: ReviewItem] {
	this.updateByAdding[Lead<:blockers, val]
}

fun addBlockingMark: set Lead {
	{l: Lead,  val: ReviewItem| l.addBlockingMark[val]}.ReviewItem
}

pred Lead.removeBlockingMark[val: ReviewItem] {
	this.updateByRemoving[Lead<:blockers, val]
}

fun removeBlockingMark: set Lead {
	{l: Lead,  val: ReviewItem| l.removeBlockingMark[val]}.ReviewItem
}

fun Lead.findItems: set ReviewItem {
	this.leadItems
}

fun Lead.findBlockingItems: set ReviewItem {
	{i: ReviewItem | i in this.blockers and i in this.findItems}
}

fun Lead.findStageItems: set ReviewItem {
	this.stageItems[LeadStage]
}

fun Lead.findStageItems[stg: LeadStage]: set ReviewItem {
	this.stageItems[stg]
}

fun Lead.findBlockingStageItems: set ReviewItem {
	{i: ReviewItem | i in this.blockers and i in this.findStageItems}
}

fun Lead.findBlockingStageItems[stg: LeadStage]: set ReviewItem {
	{i: ReviewItem | i in this.blockers and i in this.findStageItems[stg]}
}

fun Lead.findAllItems: set ReviewItem {
	this.findItems + this.findStageItems
}

fun Lead.findAllBlockingItems: set ReviewItem {
	this.findBlockingItems + this.findBlockingStageItems
}

fun Lead.stageOf[itm: ReviewItem]: lone LeadStage {
	itm in this.findItems implies none else this.stageItems.itm
}
```

## Invariants

```alloy
pred leadCreateState {
	all led: createLead {
		led.status = ActiveLeadStatus
		led.stage = LeadStage1
		led.leadItems = none
		led.stageItems = none -> none
		led.blockers = none
	}
}

pred uniqueLead {
	no disj led1,led2: Lead | led1.asset = led2.asset and led1.goal = led2.goal
}

pred cannotMoveLead {
	Lead.readOnly[Lead<:asset]
	Lead.readOnly[Lead<:goal]
}

pred allItemsArePrivate {
	no disj led1,led2: Lead | some i: ReviewItem | i in led1.findAllItems and i in led2.findAllItems
}

pred forbidDeclineAcceptSwitch {
	all led: Lead {
		led.status' = DeclinedLeadStatus => led.status != AcceptedLeadStatus
		led.status' = AcceptedLeadStatus => led.status != DeclinedLeadStatus
	}
}

pred allowChangeOnlyIfActive {
	all led: Lead {
		led.status != ActiveLeadStatus => {
			led.readOnly[Lead<:stage]
			led.readOnly[Lead<:leadItems]
			led.readOnly[Lead<:stageItems]
			led.readOnly[Lead<:blockers]
		}
	}
}

pred canAcceptOnlyOnLastStage {
	all led: Lead {
		led.accept => led.stage = LeadStage3 and led.stage' = LeadStage3
	}
}

pred cannotSkipStage {
	no led: Lead {
		(led.stage = LeadStage1 and led.stage' = LeadStage3) or (led.stage = LeadStage3 and led.stage' = LeadStage1)
	}
}

pred itemInLeadXOrInStage {
	no led: Lead {
		some itm: ReviewItem | itm in led.findStageItems and itm in led.findItems
	}
}

pred blockersInAllReviewItems {
	all led: Lead {
		led.blockers in led.findAllItems
	}
}

pred blockersBlocksStage {
	all led: Lead {
		some led.findBlockingStageItems[led.stage] implies (led.stage = led.stage' or led.stage'.isBefore[led.stage])
	}
}

pred blockersBlocksLead {
	all led: Lead {
		some led.findAllBlockingItems implies (not led.accept and not led.decline)
	}
}

fact{
	always {
		leadCreateState
		uniqueLead
		cannotMoveLead
		allItemsArePrivate
		forbidDeclineAcceptSwitch
		allowChangeOnlyIfActive
		canAcceptOnlyOnLastStage
		cannotSkipStage
		itemInLeadXOrInStage
		blockersInAllReviewItems
		blockersBlocksStage
		blockersBlocksLead
	}
}
```

## Visualization

```alloy
enum LeadEvent{
	CreateLead, 
	DeleteLead, 
	AcceptLead, 
	DeclineLead, 
	ReopenLead,
	NextStageLead, 
	PreviousStageLead,
	AddItemsLead, 
	RemoveItemsLead,
	AddBlockingMarkLead,
	RemoveBlockingMarkLead
}

fun vizLeadEvents: set LeadEvent {
	vizLeadEventArgs.Lead
}

fun vizLeadEventArgs: LeadEvent -> Lead {
	CreateLead -> createLead
	+ DeleteLead -> deleteLead
	+ AcceptLead -> accept
	+ DeclineLead -> decline
	+ ReopenLead -> reopen
	+ NextStageLead -> nextStage
	+ PreviousStageLead -> previousStage
	+ AddItemsLead -> (addItems + addStageItems)
	+ RemoveItemsLead -> (removeItems + removeStageItems)
	+ AddBlockingMarkLead -> addBlockingMark
	+ RemoveBlockingMarkLead -> removeBlockingMark
}
```

## Simulations

```alloy
pred acceptLeadPrinciple {
	always #vizLeadEvents <= 1
	eventually (some accept and once some addBlockingMark)
} 

pred declineLeadPrinciple {
	always #vizLeadEvents <= 1
	eventually (some decline and once some addBlockingMark)
}

run acceptLeadPrinciple
run declineLeadPrinciple
```
