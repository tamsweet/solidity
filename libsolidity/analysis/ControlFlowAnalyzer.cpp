/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolidity/analysis/ControlFlowAnalyzer.h>

#include <liblangutil/SourceLocation.h>
#include <libsolutil/Algorithms.h>

#include <range/v3/algorithm/sort.hpp>

#include <functional>

using namespace std::placeholders;
using namespace solidity::langutil;
using namespace solidity::frontend;


/**
 * @brief Executes the control flow analysis on all functions in the CFG.
 *
 * This function iterates through all functions and their associated control
 * flow graphs (CFGs) stored in the `m_cfg` object (presumably a member
 * of the `ControlFlowAnalyzer` class). It then calls the `analyze`
 * function (defined elsewhere) to perform control flow analysis on
 * each function.
 *
 * @return true if the control flow analysis completes without errors for
 *         all functions. Returns false if any errors are found.
 */
bool ControlFlowAnalyzer::run()
{
	// 1. Iterate through all function flows in the control flow graph:
	//    - m_cfg.allFunctionFlows() likely returns a collection (e.g., map or vector)
	//      where each element represents a function and its associated CFG.
	for (auto& [pair, flow]: m_cfg.allFunctionFlows())
	{
		// 2. Analyze each function's control flow:
		//    - Call the 'analyze' function (implementation not shown here),
		//      passing the function definition, the contract it belongs to, and its CFG.
		analyze(*pair.function, pair.contract, *flow);
	}

	// 3. Check for errors and return the result:
	//    - After analyzing all functions, check if any errors were reported
	//      during the analysis. Return 'true' if no errors, 'false' otherwise.
	return !Error::containsErrors(m_errorReporter.errors());
}
/*
Explanation:
	1. Iteration over Function Flows: The code begins by iterating through all the function flows in the control flow
graph (m_cfg.allFunctionFlows()). This likely provides a way to access each function and its associated control flow
information. The structure returned by allFunctionFlows probably contains: ○ pair: This likely holds a reference to the
FunctionDefinition object and the ContractDefinition object to which the function belongs. ○ flow: This most likely
represents the Control Flow Graph (CFG) for the function.
	2. Control Flow Analysis: For each function, the analyze function is called, passing:
		○ *pair.function: A pointer (or reference) to the FunctionDefinition object, providing information about the
function's signature, parameters, etc. ○ pair.contract: A pointer (or reference) to the ContractDefinition object,
representing the contract to which the function belongs. ○ *flow: A pointer (or reference) to the CFG, which is a graph
representation of the function's control flow. Error Checking and Return: After analyzing all the functions, the run
function checks if any errors were encountered during the control flow analysis. It uses
Error::containsErrors(m_errorReporter.errors()) to see if the ErrorReporter (a mechanism for collecting errors) contains
any reported errors. The function returns true if no errors were found and false otherwise.
*/


/**
 * @brief Performs control flow analysis on a single function.
 *
 * This function is responsible for running specific control flow
 * related checks on a given function's CFG.
 *
 * @param _function    A constant reference to the FunctionDefinition of the
 *                     function being analyzed.
 * @param _contract     A pointer to the ContractDefinition of the contract
 *                     containing the function (can be null).
 * @param _flow        A constant reference to the FunctionFlow object
 *                     representing the function's control flow graph.
 */
void ControlFlowAnalyzer::analyze(
	FunctionDefinition const& _function, ContractDefinition const* _contract, FunctionFlow const& _flow)
{
	// 1. Skip analysis for unimplemented functions:
	//    - (Abstract functions, external functions without a body, etc.)
	if (!_function.isImplemented())
	{
		return;
	}

	// 2. Determine if the most derived contract name needs to be tracked:
	std::optional<std::string> mostDerivedContractName;

	// The most derived contract's name is only needed if it's different
	// from the function's directly enclosing contract. This might be
	// relevant in inheritance scenarios where the analysis is done on an
	// overridden function.
	if (_contract && _contract != _function.annotation().contract)
	{
		mostDerivedContractName = _contract->name();
	}

	// 3. Perform uninitialized access check:
	//    - Check if variables are accessed before being initialized.
	checkUninitializedAccess(
		_flow.entry,						   // Entry point of the CFG
		_flow.exit,							   // Exit point of the CFG
		_function.body().statements().empty(), // True if the function body is empty
		mostDerivedContractName				   // Most derived contract name (optional)
	);

	// 4. Perform unreachable code check:
	//    - Check if there are any unreachable code blocks in the CFG.
	checkUnreachable(
		_flow.entry,			// Entry point of the CFG
		_flow.exit,				// Exit point of the CFG
		_flow.revert,			// Set of revert points in the CFG
		_flow.transactionReturn // Set of transaction return points in the CFG
	);

	// ... (Potentially other control flow checks can be added here.)
}
/*
Explanation:
	1. Skip Unimplemented Functions: The function first checks if the given _function is actually implemented using
!_function.isImplemented(). It skips the analysis if the function is abstract, external without a body, or otherwise not
fully implemented.
	2. Most Derived Contract Name: The variable mostDerivedContractName is declared as a std::optional<std::string>.
This variable is used to store the name of the most derived contract in the inheritance hierarchy where the function is
being called. This information might be required for more precise error reporting, especially if the function being
analyzed is an overridden function from a base contract.
	3. Uninitialized Access Check: The function calls checkUninitializedAccess to perform analysis related to variables
being accessed before being initialized. It passes the entry and exit points of the CFG, a boolean indicating if the
function body is empty, and the optional mostDerivedContractName. Unreachable Code Check: The function calls
checkUnreachable to find any unreachable blocks of code within the function's CFG. This check likely uses the CFG
structure and information about revert points and transaction return points to determine code reachability.

Example (Illustrative):
// Assume _function represents the following Solidity function:
//
// function myFunction(uint x) public {
//    uint y;
//    if (x > 10) {
//        y = x * 2;
//    }
//    // Warning: 'y' might be used uninitialized here!
//    z = y + 5;
// }
*/


/**
 * @brief Checks for uninitialized variable accesses within a function's control flow.
 *
 * This function analyzes the control flow graph (CFG) of a function to identify
 * any potential accesses to variables before they have been assigned a value.
 * It reports errors for accesses to storage or calldata pointers without initialization
 * and warnings for unnamed return variables that may remain unassigned.
 *
 * @param _entry              A pointer to the entry CFGNode of the function.
 * @param _exit               A pointer to the exit CFGNode of the function.
 * @param _emptyBody           True if the function body is empty (no statements).
 * @param _contractName        An optional string containing the name of the most derived
 *                             contract in the inheritance hierarchy (if applicable).
 */
void ControlFlowAnalyzer::checkUninitializedAccess(
	CFGNode const* _entry, CFGNode const* _exit, bool _emptyBody, std::optional<std::string> _contractName)
{
	// 1. Define a struct to store information about each node in the CFG:
	struct NodeInfo
	{
		std::set<VariableDeclaration const*> unassignedVariablesAtEntry; ///< Set of unassigned variables at node entry
		std::set<VariableDeclaration const*> unassignedVariablesAtExit;	 ///< Set of unassigned variables at node exit
		std::set<VariableOccurrence const*>
			uninitializedVariableAccesses; ///< Set of uninitialized variable accesses within the node

		/**
		 * @brief Propagates uninitialized variable information from an entry node to this node.
		 *
		 * @param _entryNode The NodeInfo of the entry node from which to propagate information.
		 * @return true if new variables were added, indicating that the current node needs to be
		 *         re-traversed; false otherwise.
		 */
		bool propagateFrom(NodeInfo const& _entryNode)
		{
			// Store previous sizes for comparison
			size_t previousUnassignedVariablesAtEntry = unassignedVariablesAtEntry.size();
			size_t previousUninitializedVariableAccessess = uninitializedVariableAccesses.size();

			// Merge unassigned variables and accesses from the entry node
			unassignedVariablesAtEntry += _entryNode.unassignedVariablesAtExit;
			uninitializedVariableAccesses += _entryNode.uninitializedVariableAccesses;

			// Return true if new variables or accesses were added
			return unassignedVariablesAtEntry.size() > previousUnassignedVariablesAtEntry
				   || uninitializedVariableAccesses.size() > previousUninitializedVariableAccessess;
		}
	};

	// 2. Create a map to store NodeInfo for each CFG node:
	std::map<CFGNode const*, NodeInfo> nodeInfos;

	// 3. Create a set to track nodes that need to be traversed:
	std::set<CFGNode const*> nodesToTraverse;
	nodesToTraverse.insert(_entry); // Start with the entry node.

	// 4. Traverse the CFG to analyze variable initialization:
	//    - Loop until there are no more nodes to traverse.
	while (!nodesToTraverse.empty())
	{
		// 4.1 Get the first node from the set and remove it from the traversal set
		CFGNode const* currentNode = *nodesToTraverse.begin();
		nodesToTraverse.erase(nodesToTraverse.begin());

		// 4.2 Get (or create) the NodeInfo for the current node
		auto& nodeInfo = nodeInfos[currentNode];

		// 4.3 Copy the unassigned variables at entry
		auto unassignedVariables = nodeInfo.unassignedVariablesAtEntry;

		// 4.4 Iterate through variable occurrences within the current node
		for (auto const& variableOccurrence: currentNode->variableOccurrences)
		{
			// 4.5 Analyze each variable occurrence based on its kind:
			switch (variableOccurrence.kind())
			{
			case VariableOccurrence::Kind::Assignment:
				// If it's an assignment, remove the variable from the unassigned set.
				unassignedVariables.erase(&variableOccurrence.declaration());
				break;
			case VariableOccurrence::Kind::InlineAssembly:
				// For now, consider all variables in inline assembly as accessed.
				// (Further analysis of assembly might be added later.)
				// fallthrough // Intentional fallthrough to the 'Access' case
			case VariableOccurrence::Kind::Access:
			case VariableOccurrence::Kind::Return:
				// If the variable is accessed, returned, or used in inline assembly:
				if (unassignedVariables.count(&variableOccurrence.declaration()))
				{
					// If the variable is unassigned at this point, record
					// the uninitialized access in the NodeInfo.
					nodeInfo.uninitializedVariableAccesses.insert(&variableOccurrence);
				}
				break;
			case VariableOccurrence::Kind::Declaration:
				// If it's a variable declaration, add it to the unassigned set.
				unassignedVariables.insert(&variableOccurrence.declaration());
				break;
			}
		}
		// 4.6 Update the unassigned variables at exit for the current node
		nodeInfo.unassignedVariablesAtExit = std::move(unassignedVariables);

		// 4.7 Propagate information to exit nodes and queue them for traversal:
		for (auto const& exit: currentNode->exits)
		{
			// Propagate information from the current node to the exit node
			if (auto exists = util::valueOrNullptr(nodeInfos, exit); nodeInfos[exit].propagateFrom(nodeInfo) || !exists)
			{
				// If propagation resulted in changes or if the exit node hasn't been visited,
				// add it to the set of nodes to traverse.
				nodesToTraverse.insert(exit);
			}
		}
	}

	// 5. Check for uninitialized accesses at the function exit:
	auto const& exitInfo = nodeInfos[_exit];
	if (!exitInfo.uninitializedVariableAccesses.empty())
	{
		// 5.1. Order the uninitialized accesses for consistent error reporting:
		std::vector<VariableOccurrence const*> uninitializedAccessesOrdered(
			exitInfo.uninitializedVariableAccesses.begin(), exitInfo.uninitializedVariableAccesses.end());
		ranges::sort(
			uninitializedAccessesOrdered,
			[](VariableOccurrence const* lhs, VariableOccurrence const* rhs) -> bool { return *lhs < *rhs; });

		// 5.2. Report errors or warnings for each uninitialized access:
		for (auto const* variableOccurrence: uninitializedAccessesOrdered)
		{
			VariableDeclaration const& varDecl = variableOccurrence->declaration();

			// Create a SecondarySourceLocation for additional error context.
			SecondarySourceLocation ssl;
			if (variableOccurrence->occurrence())
			{
				ssl.append("The variable was declared here.", varDecl.location());
			}

			// 5.2.1. Check for uninitialized storage or calldata pointer accesses:
			bool isStorage = varDecl.type()->dataStoredIn(DataLocation::Storage);
			bool isCalldata = varDecl.type()->dataStoredIn(DataLocation::CallData);
			if (isStorage || isCalldata)
			{
				m_errorReporter.typeError(
					3464_error,
					variableOccurrence->occurrence() ? *variableOccurrence->occurrence() : varDecl.location(),
					ssl,
					"This variable is of " + std::string(isStorage ? "storage" : "calldata")
						+ " pointer type and can be "
						+ (variableOccurrence->kind() == VariableOccurrence::Kind::Return ? "returned" : "accessed")
						+ " without prior assignment, which would lead to undefined behaviour.");
			}
			else if (!_emptyBody && varDecl.name().empty())
			{
				// 5.2.2. Check for unnamed return variables that might be unassigned:
				if (!m_unassignedReturnVarsAlreadyWarnedFor.emplace(&varDecl).second)
				{
					continue; // Skip reporting if already warned for this variable
				}

				m_errorReporter.warning(
					6321_error,
					varDecl.location(),
					"Unnamed return variable can remain unassigned"
						+ (_contractName.has_value() ? " when the function is called when \"" + _contractName.value()
														   + "\" is the most derived contract."
													 : ".")
						+ " Add an explicit return with value to all non-reverting code paths or name the variable.");
			}
		}
	}
}

/**
 * @brief Checks for unreachable code blocks within a function's control flow graph (CFG).
 *
 * This function identifies and reports warnings for code segments that are unreachable
 * based on the structure of the CFG. It uses breadth-first search to traverse the graph
 * and determine which nodes are reachable from the entry point.
 *
 * @param _entry              A pointer to the entry CFGNode of the function.
 * @param _exit               A pointer to the exit CFGNode of the function.
 * @param _revert              A pointer to the CFGNode representing the revert point (if any).
 * @param _transactionReturn  A pointer to the CFGNode representing the transaction return
 *                            point (if any).
 */
void ControlFlowAnalyzer::checkUnreachable(
	CFGNode const* _entry, CFGNode const* _exit, CFGNode const* _revert, CFGNode const* _transactionReturn)
{
	// 1. Find all reachable nodes from the entry point:
	//    - Use a breadth-first search (BFS) algorithm from the 'util' namespace.
	//    - The lambda function passed to 'run' defines how to traverse the graph
	//      (by adding each exit node of a node to the queue).
	std::set<CFGNode const*> reachable = util::BreadthFirstSearch<CFGNode const*>{{_entry}}
											 .run(
												 [](CFGNode const* _node, auto&& _addChild)
												 {
													 for (CFGNode const* exit: _node->exits)
													 {
														 _addChild(exit);
													 }
												 })
											 .visited; // Get the set of visited (reachable) nodes.

	// 2. Find unreachable nodes by traversing backward from exit points:
	//    - Create a set to store the source locations of unreachable nodes.
	std::set<SourceLocation> unreachable;

	//    - Run a BFS starting from the exit, revert, and transaction return nodes.
	util::BreadthFirstSearch<CFGNode const*>{{_exit, _revert, _transactionReturn}}.run(
		[&](CFGNode const* _node, auto&& _addChild)
		{
			// If a node is not in the 'reachable' set and has a valid source location...
			if (!reachable.count(_node) && _node->location.isValid())
			{
				// ...add its location to the 'unreachable' set.
				unreachable.insert(_node->location);
			}

			// Add the entry nodes of the current node to the queue for backward traversal.
			for (CFGNode const* entry: _node->entries)
			{
				_addChild(entry);
			}
		});

	// 3. Report warnings for unreachable code blocks:
	for (auto it = unreachable.begin(); it != unreachable.end();)
	{
		// 3.1. Get the current unreachable source location:
		SourceLocation location = *it++;

		// 3.2. Extend the location to cover consecutive unreachable lines:
		for (; it != unreachable.end() && it->start <= location.end; ++it)
		{
			location.end = std::max(location.end, it->end);
		}

		// 3.3. Report a warning if this location hasn't been warned about before:
		if (m_unreachableLocationsAlreadyWarnedFor.emplace(location).second)
		{
			m_errorReporter.warning(5740_error, location, "Unreachable code.");
		}
	}
}
/*
Explanation:
	1. Reachable Node Identification: The function first performs a breadth-first search (BFS) starting from the entry
node (_entry). The BFS explores all possible paths in the CFG and marks nodes as visited (reachable). The reachable set
stores all the reachable nodes.
	2. Unreachable Node Identification:
		○ A std::set<SourceLocation> called unreachable is created to store the locations of unreachable code blocks.
		○ Another BFS is performed, but this time starting from the exit points of the function: the exit node (_exit),
the revert node (_revert), and the transaction return node (_transactionReturn). This BFS traverses the graph backward
(from exit points to entry points). ○ During the backward BFS, if a node is encountered that is not present in the
reachable set (meaning it was not reached by the forward BFS), and the node has a valid source location, its location is
added to the unreachable set.
	3. Warning Reporting:
		○ The code iterates through the unreachable set (which is likely sorted by source location).
		○ It extends the location of an unreachable block to cover consecutive unreachable lines of code.
To avoid duplicate warnings for the same location, a set called m_unreachableLocationsAlreadyWarnedFor is used to keep
track of locations that have already been reported. If a location has not been warned about before, a warning
(5740_error) is emitted, indicating that the code is unreachable.

Example:
function myFunction(uint x) public {
    if (x > 10) {
        // ... some code ...
    } else {
        revert(); // This path makes subsequent code unreachable
    }
    // Unreachable code:
    x = x * 2;  
    // ... more unreachable code ... 
}
In this example:
The forward BFS would mark all nodes up to the revert() statement as reachable.
The backward BFS, starting from the revert() node, would find the code after the revert() to be unreachable.
checkUnreachable would report a warning about the unreachable code, indicating the source location.
*/
