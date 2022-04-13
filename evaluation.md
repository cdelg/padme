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
fun createEvaluation: set Evaluation {
	{e: Evaluation | e.create}
}

fun deleteEvaluation: set Evaluation {
	{e: Evaluation | e.delete}
}

pred Evaluation.editName[nam: Text] {
	this.update[Evaluation<:name, nam]
}

fun editName: set Evaluation {
	{e: Evaluation, txt: Text | e.editName[txt]}.Text + {e: Evaluation | e.editName[none]}
}

pred Evaluation.changeOwner[owr: Participant] {
	this.update[Evaluation<:functionalOwner, owr]
}

fun changeOwner: set Evaluation {
	{e: Evaluation, owr: Participant | e.changeOwner[owr]}.Participant
}

pred Evaluation.invite[inv: Participant] {
	this.updateByAdding[Evaluation<:invited, inv]
}

fun invite: set Evaluation {
	{e: Evaluation, inv: Participant | e.invite[inv]}.Participant
}

pred Evaluation.cancelInvite[inv: Participant] {
	this.updateByRemoving[Evaluation<:invited, inv]
}

fun cancelInvite: set Evaluation {
	{e: Evaluation, inv: Participant | e.cancelInvite[inv]}.Participant
}

pred Evaluation.reorderSections {
	some i: Int | this.update[Evaluation<:sectionsOrder, i]
}

fun reorderSections: set Evaluation {
	{e: Evaluation | e.reorderSections}
}

// EvaluationSection
fun addEvaluationSection: set EvaluationSection {
	{e: EvaluationSection | e.create}
}

fun removeEvaluationSection: set EvaluationSection {
	{e: EvaluationSection | e.delete}
}

pred EvaluationSection.editSectionName[nam: Text] {
	this.update[EvaluationSection<:name, nam]
}

fun editSectionName: set EvaluationSection {
	{e: EvaluationSection, txt: Text | e.editSectionName[txt]}.Text + {e: EvaluationSection | e.editSectionName[none]}
}

pred EvaluationSection.editGuidelines[gud: Text] {
	this.update[EvaluationSection<:guidelines, gud]
}

fun editGuidelines: set EvaluationSection {
	{e: EvaluationSection, txt: Text | e.editGuidelines[txt]}.Text + {e: EvaluationSection | e.editGuidelines[none]}
}

pred EvaluationSection.reorderBlocks {
	some i: Int | this.update[EvaluationSection<:blocksOrder, i]
}

fun reorderBlocks: set EvaluationSection {
	{e: EvaluationSection | e.reorderBlocks}
}

// Block
fun addAssessmentBlock: set AssessmentBlock {
	{e: AssessmentBlock | e.create}
}

fun removeAssessmentBlock: set AssessmentBlock {
	{e: AssessmentBlock | e.delete}
}

pred AssessmentBlock.editAssessmentTitle[ttl: Text] {
	this.update[AssessmentBlock<:title, ttl]
}

fun editAssessmentTitle: set AssessmentBlock {
	{e: AssessmentBlock, txt: Text | e.editAssessmentTitle[txt]}.Text + {e: AssessmentBlock | e.editAssessmentTitle[none]}
}

pred AssessmentBlock.editAssessment[ast: Text] {
	this.update[AssessmentBlock<:assessment, ast]
}

fun editAssessment: set AssessmentBlock {
	{e: AssessmentBlock, txt: Text | e.editAssessment[txt]}.Text + {e: AssessmentBlock | e.editAssessment[none]}
}

fun addQuestionBlock: set QuestionBlock {
	{e: QuestionBlock | e.create}
}

fun removeQuestionBlock: set QuestionBlock {
	{e: QuestionBlock | e.delete}
}

pred QuestionBlock.editQuestion[qst: Text] {
	this.update[QuestionBlock<:question, qst]
}

fun editQuestion: set QuestionBlock {
	{e: QuestionBlock, txt: Text | e.editQuestion[txt]}.Text + {e: QuestionBlock | e.editQuestion[none]}
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
	CreateEvaluation, 
	DeleteEvaluation, 
	EditNameEvaluation, 
	ChangeOwnerEvaluation, 
	InviteEvaluation, 
	CancelInviteEvaluation, 
	AddSectionEvaluation, 
	RemoveSectionEvaluation, 
	ReorderSectionEvaluation, 
	EditSectionNameEvaluation, 
	EditGuidelinesEvaluation, 
	AddBlockEvaluation, 
	RemoveBlockEvaluation, 
 	ReorderBlockEvaluation, 
	EditAssessmentTitleEvaluation, 
	EditAssessmentEvaluation, 
	EditQuestionEvaluation
}

fun vizEvaluationEvents: set univ {
	vizEvaluationEventArgs.univ
}

fun vizEvaluationEventArgs: EvaluationEvent -> univ {
	CreateEvaluation -> {e: Evaluation | e.create}
	+ DeleteEvaluation -> {e: Evaluation | e.delete}
	+ EditNameEvaluation -> editName
	+ ChangeOwnerEvaluation -> changeOwner
	+ InviteEvaluation -> invite
	+ CancelInviteEvaluation -> cancelInvite
	+ AddSectionEvaluation -> addEvaluationSection
	+ RemoveSectionEvaluation -> removeEvaluationSection
	+ ReorderSectionEvaluation -> reorderSections
	+ EditSectionNameEvaluation -> editName
	+ EditGuidelinesEvaluation -> editGuidelines
	+ AddBlockEvaluation -> (addAssessmentBlock + addQuestionBlock)
	+ RemoveBlockEvaluation -> (removeAssessmentBlock + removeQuestionBlock)
	+ ReorderBlockEvaluation -> reorderBlocks
	+ EditAssessmentTitleEvaluation -> editAssessmentTitle
	+ EditAssessmentEvaluation -> editAssessment
	+ EditQuestionEvaluation -> editQuestion
}
```

## Simulations

```alloy
pred evaluatePrinciple {
	always #vizEvaluationEvents <= 2
	eventually (some addAssessmentBlock and some invite)
}

run evaluatePrinciple
```
