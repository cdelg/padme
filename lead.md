---

---

# Lead

A lead allows you to review an asset against a goal by following a workflow.

```alloy
module lead[Asset, Goal, ReviewItem]

open fwk/fwk
open fwk/ordered_value[LeadStage1, LeadStage2, LeadStage3]
```

## State

```alloy
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
pred Lead.accept {
	this.update[Lead<:status, AcceptedLeadStatus]
}

pred Lead.decline {
	this.update[Lead<:status, DeclinedLeadStatus]
}

pred Lead.reopen {
	this.update[Lead<:status, ActiveLeadStatus]
}

pred Lead.nextStage {
	this.update[Lead<:stage] and this.stage'.isAfter[this.stage]
}

pred Lead.previousStage {
	this.update[Lead<:stage] and this.stage'.isBefore[this.stage]
}

pred Lead.addItems {
	this.updateByAdding[Lead<:leadItems] or this.addStageItems
}

pred Lead.addItems[val: ReviewItem] {
	this.updateByAdding[Lead<:leadItems, val] or this.addStageItems[val]
}

pred Lead.addItems[stg: LeadStage, val: ReviewItem] {
	stg = none implies this.updateByAdding[Lead<:leadItems, val] else this.addStageItems[stg, val]
}

private pred Lead.addStageItems {
	some stg: LeadStage, val: ReviewItem | this.addStageItems[stg, val]	
}

private pred Lead.addStageItems[val: ReviewItem] {
	some stg: LeadStage | this.addStageItems[stg, val]
}

private pred Lead.addStageItems[stg: LeadStage, val: ReviewItem] {
	some val
	some LeadStage
	this.canUpdate
	all o: this | val not in o.stageItems[stg] and val in o.stageItems'[stg]	
}

pred Lead.removeItems {
	this.updateByRemoving[Lead<:leadItems] or some stg: LeadStage, val: ReviewItem | this.removeStageItems[stg, val]
}

pred Lead.removeItems[val: ReviewItem] {
	this.updateByRemoving[Lead<:leadItems, val] or some stg: LeadStage | this.removeStageItems[stg, val]
}

private pred Lead.removeStageItems[stg: LeadStage, val: ReviewItem] {
	some val
	some LeadStage
	this.canUpdate
	all o: this | val in o.stageItems[stg] and val not in o.stageItems'[stg]
}

pred Lead.addBlockingMark {
	this.updateByAdding[Lead<:blockers]
}

pred Lead.addBlockingMark[val: ReviewItem] {
	this.updateByAdding[Lead<:blockers, val]
}

pred Lead.removeBlockingMark {
	this.updateByRemoving[Lead<:blockers]
}

pred Lead.removeBlockingMark[val: ReviewItem] {
	this.updateByRemoving[Lead<:blockers, val]
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
	all led: {e: Lead | e.created} {
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
	CreatedLead, 
	DeletedLead, 
	AcceptedLead, 
	DeclinedLead, 
	ReopenedLead,
	NextStage, 
	PreviousStage,
	AddedItems, 
	RemovedItems,
	AddedBlockingMark,
	RemovedBlockingMark
}

fun leadEvents: univ -> univ {
	CreatedLead -> {t: Lead | t.created}
	+ DeletedLead -> {t: Lead |  t.delete}
	+ AcceptedLead -> {t: Lead | before t.accept}
	+ DeclinedLead -> {t: Lead | before t.decline}
	+ ReopenedLead -> {t: Lead | before t.reopen}
	+ NextStage -> {t: Lead | before t.nextStage}
	+ PreviousStage -> {t: Lead | before t.previousStage}
	+ AddedItems -> {t: Lead | before t.addItems}
	+ RemovedItems -> {t: Lead | before t.removeItems}
	+ AddedBlockingMark -> {t: Lead | before t.addBlockingMark}
	+ RemovedBlockingMark -> {t: Lead | before t.removeBlockingMark}
}
```

## Simulations

```alloy
pred acceptLeadPrinciple {
	always #leadEvents <= 1
	eventually some led: Lead | (led.accept and once led.addBlockingMark)
} 

pred declineLeadPrinciple {
	always #leadEvents <= 1
	eventually some led: Lead | led.decline and once led.addBlockingMark
}

run acceptLeadPrinciple
run declineLeadPrinciple
```
