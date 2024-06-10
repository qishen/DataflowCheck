// Define basic entities
abstract sig Entity {}
sig Computation extends Entity {}
sig DataFlow extends Entity {}

// Define time
abstract sig Time {}
one sig InitialTime extends Time {}

// Define the state of computations at different times
sig ComputationState {
    	computation: Computation,
    	state: set Data,
    	time: Time
}

// Define the state of data flows at different times
sig DataFlowState {
    	dataflow: DataFlow,
    	inputState: DataState,
    	outputState: DataState,
    	time: Time
}


sig Data {
	key: Data,
	val: Data,
	// (key, val) connects to (val, x), which connects to (x, y) and so on.
	// `connected` is a set of instances of type Data that its key `d.key` equals to `val` but ideally it should be seperated from Data.
	connected: set Data
}

fact {
	all d : Data | d.connected.key = d.val
}

// No self-cycle allowed in Data and its components that are also of type Data.
fact {
	no d: Data | d in d.^(key + val) 
}

// Define the state of data at different times
sig DataState {
	data: set Data,
    	time: Time,
	// The next state after one iteration in the cycle of a sub-dataflow.
	nxt: DataState
}{
	// The hardcoded constraint between one state and another state after one iteration
	SingleIterationOperation[this, nxt]
}

fact {
	no ds: DataState | ds = ds.nxt
}

// Operator: Map - (a, b) to (x, y)
sig MapOperator extends Entity {
    	operation: Data -> Data
}

// Operator: Filter (a, b) to a singleton
sig FilterOperator extends Entity {
    	condition: Data -> lone Data
}

// Operator: Join - (a, b) joins (a, c) = (a, (b, c))
sig JoinOperator extends Entity {}

// Operator: Concat
sig ConcatOperator extends Entity {}

// Define operations that transition the system from one state to another
pred MapOperation[op: MapOperator, state: DataState, newState: DataState] {
	// Apply map operation to each data element
	newState.data = op.operation[state.data]
}

pred FilterOperation[op: FilterOperator, state: DataState, newState: DataState] {
	// Apply filter operation based on condition and add it to the new state only if it is mapped to a singleton and not empty
   	newState.data = { d: Data | d in state.data && op.condition[d] != none }
}

pred JoinOperation[state1: DataState, state2: DataState, newState: DataState] {
    	//  Data { key: d1.key, val: Data {d1.val, d2.val }}
	newState.data = { 
		// Find all Data that its key is in the keys of both state1 and state2
		// Since state.data is a set of Data, state.data.key is set of keys as well.
		d: Data |  d.key in state1.data.key && 
				d.key in state2.data.key &&
				// The val of d is composed of the vals of two Data from state1 and state2
				d.val.key in state1.data.val &&
				d.val.val in state2.data.val
	}
}

pred ConcatOperation[state1: DataState, state2: DataState, newState: DataState] {
	newState.data = state1.data + state2.data
}

pred KeyValSwapOperation [initState: DataState, endState: DataState] {
	one mop: MapOperator | all data: Data |
	let mappedData = mop.operation[data] |
	// Map (a, b) to (b, a)
	data.key = mappedData.val && 
	data.val = mappedData.key &&
	MapOperation[mop, initState, endState]
}

pred MapAndJoinOperation [initState: DataState, endState: DataState] {
	// Flip (a, b) and join with itself
	one interState: DataState |
	KeyValSwapOperation[initState, interState] &&
	JoinOperation[initState, interState, endState]
}

pred JoinResultMapOperation [initState: DataState, endState: DataState] {
	one mop: MapOperator | all data: Data |
	let mappedData = mop.operation[data] |	
	// Map (a, (b, c)) to (b, c)
	data.val.key = mappedData.key && 
	data.val.val = mappedData.val &&
	MapOperation[mop, initState, endState]
}

pred SingleIterationOperation [initState: DataState, endState: DataState] {
	some s1, s2: DataState |
	// (a, b) to (b, a)
	MapAndJoinOperation[initState, s1] &&
	// (a, (b, c)) to (b, c) 
	JoinResultMapOperation[s1, s2] &&
	// initState: (a, b) + s2: (b, c) = endState
	ConcatOperation[initState, s2, endState]
}

pred RepeatedIterationOperation [initState: DataState, endState: DataState] {
	// The constraint is hardcoded in DataState signature so the nxt state is computed after one iteration
	endState = initState.^nxt
}

pred DataflowResultEqualsToTransitiveClosure [initState: DataState] {
	// An end state exists that the computed dataset in itself is equal to computation of a transitive closure of all the data inside initState.
	all endState: DataState |  RepeatedIterationOperation[initState, endState] && initState.data.^connected = endState.data
}

pred UpdateDataFlow[state: DataFlowState, newState: DataFlowState] {
 	// Define rules for how data flows from input to output
   	newState.inputState = state.inputState
   	newState.outputState.data = state.inputState.data
}

// Define properties and invariants that must hold in the system
pred ConsistencyInvariant {
   	// Specify conditions that ensure the system remains consistent
   	// For example, ensure that output of one computation matches the input of another
   	all df: DataFlowState | {
        	df.outputState.data = df.inputState.data
    	}
}

// Run simulations or checks to verify properties of the model
run DataflowResultEqualsToTransitiveClosure for 5
