---

---

# Evalutation

An evaluation allows someone to collaborate with his colleagues in order to evaluate something.

```alloy
module evaluation[Participant]

open fwk/fwk
```

## State

```alloy
var sig Evaluation {
	var name: one Text, 
	var functionalOwner: one Participant,
	var invited: set Participant,
	var sectionsOrder: Int,
	var sections:  set EvaluationSection
}

enum EvaluationSectionType{AssessmentType, ParticipatoryType}

var sig EvaluationSection {
	var evaluation: one Evaluation,
	var name: lone Text,
	var guidelines: lone Text,
	var type: one EvaluationSectionType,
	var blocksOrder: Int,
	var blocks: set Block
}

let Block = (AssessmentBlock + QuestionBlock)

var sig AssessmentBlock {
	var section: one EvaluationSection,
	var title: lone Text,
	var assessment: lone Text
}

var sig QuestionBlock {
	var section: one EvaluationSection,
	var question: lone Text
}
```

## Actions

```alloy

// Evaluation
pred Evaluation.editName {
	this.update[Evaluation<:name]
}

pred Evaluation.editName[nam: Text] {
	this.update[Evaluation<:name, nam]
}

pred Evaluation.changeOwner {
	this.update[Evaluation<:functionalOwner]
}

pred Evaluation.changeOwner[owr: Participant] {
	this.update[Evaluation<:functionalOwner, owr]
}

pred Evaluation.invite {
	this.updateByAdding[Evaluation<:invited]
}

pred Evaluation.invite[inv: Participant] {
	this.updateByAdding[Evaluation<:invited, inv]
}

pred Evaluation.cancelInvite {
	this.updateByRemoving[Evaluation<:invited]
}

pred Evaluation.cancelInvite[inv: Participant] {
	this.updateByRemoving[Evaluation<:invited, inv]
}

pred Evaluation.reorderSections {
	this.update[Evaluation<:sectionsOrder]
}

// EvaluationSection
pred EvaluationSection.editName {
	this.update[EvaluationSection<:name]
}

pred EvaluationSection.editName[nam: Text] {
	this.update[EvaluationSection<:name, nam]
}

pred EvaluationSection.editGuidelines {
	this.update[EvaluationSection<:guidelines]
}

pred EvaluationSection.editGuidelines[gud: Text] {
	this.update[EvaluationSection<:guidelines, gud]
}

pred EvaluationSection.reorderBlocks {
	this.update[EvaluationSection<:blocksOrder]
}

// Block
pred AssessmentBlock.editAssessmentTitle {
	this.update[AssessmentBlock<:title]
}

pred AssessmentBlock.editAssessmentTitle[ttl: Text] {
	this.update[AssessmentBlock<:title, ttl]
}

pred AssessmentBlock.editAssessment {
	this.update[AssessmentBlock<:assessment]
}

pred AssessmentBlock.editAssessment[ast: Text] {
	this.update[AssessmentBlock<:assessment, ast]
}

pred QuestionBlock.editQuestion {
	this.update[QuestionBlock<:question]
}

pred QuestionBlock.editQuestion[qst: Text] {
	this.update[QuestionBlock<:question, qst]
}
```

## Invariants

```alloy
pred cannotChangeEvaluationOfSection {
	EvaluationSection.readOnly[EvaluationSection<:evaluation]
}

pred cannotChangeSectionOfBlock {
	AssessmentBlock.readOnly[AssessmentBlock<:section]
	QuestionBlock.readOnly[QuestionBlock<:section]
}

pred cannotChangeEvaluationType {
	EvaluationSection.readOnly[EvaluationSection<:type]
}

pred blockTypesAreFixed {
	all sec: AssessmentBlock.section | sec.type = AssessmentType
	all sec: QuestionBlock.section | sec.type = ParticipatoryType
}

pred syncSectionsSet {
	all evl: Evaluation {
		evl.sections = evl.~evaluation
	}
}

pred syncBlocksSet {
	all sec: EvaluationSection {
		sec.(blocks:>AssessmentBlock) = sec.~(AssessmentBlock<:section)
		sec.(blocks:>QuestionBlock) = sec.~(QuestionBlock<:section)
	}
}

fact{
	always {
		cannotChangeEvaluationOfSection
		cannotChangeSectionOfBlock
		cannotChangeEvaluationType
		blockTypesAreFixed
		syncSectionsSet
		syncBlocksSet
	}
}
```

## Visualization

```alloy
enum EvaluationEvent{
	CreatedEvaluation, 
	DeletedEvaluation, 
	EditedNameEvaluation, 
	ChangedOwnerEvaluation, 
	InvitedEvaluation, 
	CanceledInviteEvaluation, 
	AddedSectionEvaluation, 
	RemovedSectionEvaluation, 
	ReorderedSectionEvaluation, 
	EditedSectionNameEvaluation, 
	EditedGuidelinesEvaluation, 
	AddedBlockEvaluation, 
	RemovedBlockEvaluation, 
 	ReorderedBlockEvaluation, 
	EditedAssessmentTitleEvaluation, 
	EditedAssessmentEvaluation, 
	EditedQuestionEvaluation
}

fun evaluationEvents: univ -> univ {
	CreatedEvaluation -> {e: Evaluation | e.created}
	+ DeletedEvaluation -> {e: Evaluation | e.delete}
	+ EditedNameEvaluation -> {e: Evaluation | before e.editName}
	+ ChangedOwnerEvaluation -> {e: Evaluation | before e.changeOwner}
	+ InvitedEvaluation -> {e: Evaluation | before e.invite}
	+ CanceledInviteEvaluation -> {e: Evaluation | before e.cancelInvite}
	+ AddedSectionEvaluation -> {e: EvaluationSection |  e.created}
	+ RemovedSectionEvaluation -> {e: EvaluationSection | e.delete}
	+ ReorderedSectionEvaluation -> {e: Evaluation | before e.reorderSections}
	+ EditedSectionNameEvaluation -> {e: EvaluationSection | before e.editName}
	+ EditedGuidelinesEvaluation -> {e: EvaluationSection | before e.editGuidelines}
	+ AddedBlockEvaluation -> {e: Block | e.created}
	+ RemovedBlockEvaluation -> {e: Block | e.delete}
	+ ReorderedBlockEvaluation -> {e: EvaluationSection | before e.reorderBlocks}
	+ EditedAssessmentTitleEvaluation -> {e: AssessmentBlock | before e.editAssessmentTitle}
	+ EditedAssessmentEvaluation -> {e: AssessmentBlock | before e.editAssessment}
	+ EditedQuestionEvaluation -> {e: QuestionBlock | before e.editQuestion}
}
```

## Simulations

```alloy
pred evaluatePrinciple {
	always #evaluationEvents <= 2
	eventually some e: Evaluation {
		eventually some e.sections.blocks ; e.invite
	}
}

run evaluatePrinciple
```
