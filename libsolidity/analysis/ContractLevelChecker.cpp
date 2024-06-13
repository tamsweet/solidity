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
/**
 * Component that verifies overloads, abstract contracts, function clashes and others
 * checks at contract or function level.
 */

#include <libsolidity/analysis/ContractLevelChecker.h>

#include <liblangutil/ErrorReporter.h>
#include <libsolidity/analysis/TypeChecker.h>
#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/TypeProvider.h>
#include <libsolutil/FunctionSelector.h>

#include <fmt/format.h>

#include <range/v3/view/reverse.hpp>

using namespace solidity;
using namespace solidity::langutil;
using namespace solidity::frontend;

namespace
{ // Anonymous namespace to encapsulate helper functions

/**
 * @brief Checks if two entities, potentially representing function types, have equal
 *        parameter types when treated as externally callable functions.
 *
 * @tparam T Type of the first entity. Must be convertible to FunctionType.
 * @tparam B Type of the second entity. Must be convertible to FunctionType.
 * @param _a The first entity to compare.
 * @param _b The second entity to compare.
 * @return true if both entities, when considered as externally callable functions,
 *         have identical parameter types. Returns false otherwise.
 */
template<class T, class B>
bool hasEqualExternalCallableParameters(T const& _a, B const& _b)
{
	// Construct FunctionType objects from the input entities.
	FunctionType const& funcTypeA = FunctionType(_a);
	FunctionType const& funcTypeB = FunctionType(_b);

	// Obtain pointers to the functions representing the external callable versions
	// of the function types (removing any potential internal-only modifiers).
	auto* externalFuncA = funcTypeA.asExternallyCallableFunction(false); // false: Don't modify in-place
	auto* externalFuncB = funcTypeB.asExternallyCallableFunction(false);

	// Delegate the comparison of parameter types to the FunctionType's
	// hasEqualParameterTypes method.
	return externalFuncA->hasEqualParameterTypes(*externalFuncB);
}

/**
 * @brief Filters a map of declarations, keeping only those of a specific derived type.
 *
 * @tparam T The desired derived type of the declarations to keep.
 * @param _declarations The input map of declarations, potentially containing different
 *                     derived types.
 * @return std::map<ASTString, std::vector<T const*>> A new map containing only the
 *         declarations that are of type `T` (or a derived class of `T`). The keys of the map
 *         remain the same.
 */
template<typename T>
std::map<ASTString, std::vector<T const*>>
filterDeclarations(std::map<ASTString, std::vector<Declaration const*>> const& _declarations)
{
	std::map<ASTString, std::vector<T const*>> filteredDeclarations;

	// Iterate over each (name, overloads) pair in the input declarations map.
	for (auto const& [name, overloads]: _declarations)
	{
		// Iterate over each Declaration pointer within the 'overloads' vector.
		for (auto const* declaration: overloads)
		{
			// Attempt to dynamically cast the declaration to the desired type T.
			if (auto typedDeclaration = dynamic_cast<T const*>(declaration))
			{
				// If the cast is successful, add the casted pointer to the
				// 'filteredDeclarations' map under the same name key.
				filteredDeclarations[name].push_back(typedDeclaration);
			}
		}
	}
	return filteredDeclarations;
}

} // End of anonymous namespace

/**
 * @brief Performs high-level checks at the contract level within a Solidity source unit.
 *
 * This function checks for duplicate definitions of functions and (in the future) events.
 * It recursively checks nested contract definitions within the source unit.
 *
 * @param _sourceUnit A constant reference to the SourceUnit AST node representing the Solidity source file.
 * @return true if no errors are found during the contract-level checks; otherwise, returns false.
 */
bool ContractLevelChecker::check(SourceUnit const& _sourceUnit)
{
	bool noErrors = true;

	// 1. Check for duplicate function definitions:
	//    - `filterDeclarations<FunctionDefinition>`: Extracts function definitions
	//       from the exported symbols of the source unit.
	//    - `findDuplicateDefinitions`: Checks for and reports any duplicate function definitions
	//       (same name and parameters).
	findDuplicateDefinitions(filterDeclarations<FunctionDefinition>(*_sourceUnit.annotation().exportedSymbols));

	// 2. Check for duplicate event definitions (future feature):
	//    - Currently a placeholder, as Solidity does not yet support "free" events.
	//    - This check will become active when free events are implemented in Solidity.
	findDuplicateDefinitions(filterDeclarations<EventDefinition>(*_sourceUnit.annotation().exportedSymbols));

	// 3. Check if any errors have been reported up to this point:
	//    - If errors exist in the error reporter, set 'noErrors' to false.
	if (Error::containsErrors(m_errorReporter.errors()))
	{
		noErrors = false;
	}

	// 4. Recursively check nested contract definitions:
	//    - Iterate over all top-level AST nodes within the source unit.
	for (ASTPointer<ASTNode> const& node: _sourceUnit.nodes())
	{
		// Try to dynamically cast the node to a ContractDefinition.
		if (ContractDefinition* contract = dynamic_cast<ContractDefinition*>(node.get()))
		{
			// If the cast is successful, recursively call the 'check' function
			// on the contract definition.
			if (!check(*contract))
			{
				noErrors = false; // Propagate any errors from nested contracts.
			}
		}
	}

	return noErrors;
}
/*
Explanation:
	1. Initialization and Setup:
		○ bool noErrors = true;: A flag to track if any errors are encountered during the checks. It starts as true
assuming no errors.
	2. Duplicate Function Definition Check:
		○ The code first extracts all function definitions from the source unit's exported symbols using
filterDeclarations<FunctionDefinition>. ○ Then, it calls findDuplicateDefinitions to identify and report any functions
with the same name and parameters. This step helps enforce that all function declarations have unique signatures.
	3. Duplicate Event Definition Check (Future Feature):
		○ This section is currently inactive as Solidity doesn't yet have support for free-standing events. It's a
placeholder for a future check that will become relevant when Solidity allows defining events outside of contracts.
	4. Error Reporting Check:
		○ The code checks if any errors have been reported using Error::containsErrors(m_errorReporter.errors()). This
ensures that errors found during the duplicate definition checks are properly propagated.
	5. Recursive Check for Nested Contracts:
		○ The code iterates over all top-level nodes of the source unit.
		○ For each node, it attempts to dynamically cast it to a ContractDefinition.
		○ If the cast succeeds (meaning the node represents a contract), the check function is called recursively on
that contract definition. This ensures that the checks are performed on all contracts defined within the source unit,
including nested ones.
	6. Return Value:
The function returns noErrors, which will be false if any errors were encountered during any of the checks (duplicate
definitions or errors in nested contracts), and true otherwise.
*/

/**
 * @brief Performs various checks at the contract level for a given ContractDefinition.
 *
 * This function performs a series of checks related to function and event definitions,
 * function modifiers, constructor arguments, abstract functions, external function
 * clashes, hash collisions, library requirements, ABI compatibility, and more.
 *
 * @param _contract A constant reference to the ContractDefinition AST node representing
 *                 the contract to be checked.
 * @return true if all checks pass without errors; otherwise, returns false.
 */
bool ContractLevelChecker::check(ContractDefinition const& _contract)
{
	// 1. Initialize the 'unimplementedDeclarations' annotation:
	//    - This annotation might be used to track functions that need to be implemented
	//      (e.g., abstract functions).
	_contract.annotation().unimplementedDeclarations = std::vector<Declaration const*>();

	// 2. Perform individual checks:
	//    - Each function call below performs a specific check on the contract definition.
	checkDuplicateFunctions(_contract);			   // Check for duplicate function definitions.
	checkDuplicateEvents(_contract);			   // Check for duplicate event definitions.
	checkReceiveFunction(_contract);			   // Check the receive function (if any).
	m_overrideChecker.check(_contract);			   // Check function overrides using OverrideChecker.
	checkBaseConstructorArguments(_contract);	   // Check constructor arguments for base contracts.
	checkAbstractDefinitions(_contract);		   // Check for unimplemented abstract functions.
	checkExternalTypeClashes(_contract);		   // Check for external function type clashes.
	checkHashCollisions(_contract);				   // Check for potential hash collisions (e.g., selectors).
	checkLibraryRequirements(_contract);		   // Check for library usage and requirements.
	checkBaseABICompatibility(_contract);		   // Check ABI compatibility with base contracts.
	checkPayableFallbackWithoutReceive(_contract); // Check payable modifier usage on fallback functions.
	checkStorageSize(_contract);				   // Check the estimated storage size of the contract.

	// 3. Check for any errors and return the result:
	//    - Return true if no errors have been reported; otherwise, return false.
	return !Error::containsErrors(m_errorReporter.errors());
}

/**
 * @brief Checks for duplicate function definitions within a contract.
 *
 * This function ensures that there are no functions with the same name and
 * parameter types within a contract. It also enforces that there's at most one
 * constructor, one fallback function, and one receive ether function.
 *
 * @param _contract A constant reference to the ContractDefinition AST node
 *                 representing the contract to be checked.
 */
void ContractLevelChecker::checkDuplicateFunctions(ContractDefinition const& _contract)
{
	// 1. Initialize data structures:
	//    - `functions`: A map to store functions grouped by their names.
	//    - `constructor`, `fallback`, `receive`: Pointers to track unique
	//      constructor, fallback, and receive functions.
	std::map<std::string, std::vector<FunctionDefinition const*>> functions;
	FunctionDefinition const* constructor = nullptr;
	FunctionDefinition const* fallback = nullptr;
	FunctionDefinition const* receive = nullptr;

	// 2. Iterate over defined functions in the contract:
	for (FunctionDefinition const* function: _contract.definedFunctions())
	{
		// 3. Handle special cases (constructor, fallback, receive):
		if (function->isConstructor())
		{
			// Ensure only one constructor exists:
			if (constructor != nullptr)
			{
				// Report an error - duplicate constructor found.
				m_errorReporter.declarationError(
					7997_error,			  // Error code for duplicate constructor
					function->location(), // Location of the duplicate constructor
					SecondarySourceLocation().append("Another declaration is here:", constructor->location()),
					"More than one constructor defined." // Error message
				);
			}
			constructor = function; // Update the 'constructor' pointer.
		}
		else if (function->isFallback())
		{
			// Ensure only one fallback function exists:
			if (fallback != nullptr)
			{
				// Report an error - duplicate fallback function found.
				m_errorReporter.declarationError(
					7301_error,
					function->location(),
					SecondarySourceLocation().append("Another declaration is here:", fallback->location()),
					"Only one fallback function is allowed.");
			}
			fallback = function;
		}
		else if (function->isReceive())
		{
			// Ensure only one receive ether function exists:
			if (receive != nullptr)
			{
				// Report an error - duplicate receive function found.
				m_errorReporter.declarationError(
					4046_error,
					function->location(),
					SecondarySourceLocation().append("Another declaration is here:", receive->location()),
					"Only one receive function is allowed.");
			}
			receive = function;
		}
		else
		{
			// 4. Handle regular functions:
			//    - Ensure the function has a name.
			solAssert(!function->name().empty(), "");

			// Add the function to the 'functions' map using its name as the key.
			functions[function->name()].push_back(function);
		}
	}

	// 5. Check for duplicate regular functions (same name and parameters):
	findDuplicateDefinitions(functions);
}
/*
Explanation:
	1. Initialization: The function starts by initializing data structures to help with the checks:
		○ functions: A map that will store functions grouped by their names (keys are function names, values are vectors
of FunctionDefinition pointers). ○ constructor, fallback, receive: Pointers to keep track of whether a constructor,
fallback function, or receive ether function has been encountered. They are initially set to nullptr.
	2. Iterating through Functions: The code then iterates over each function defined within the contract using
_contract.definedFunctions().
	3. Handling Special Cases:
		○ For each function, it first checks if it's a constructor (isConstructor()), fallback (isFallback()), or
receive ether (isReceive()) function. ○ For these special cases, it ensures there's only one definition: § If a
duplicate is found, an error is reported using m_errorReporter.declarationError(), providing details about the error and
its location. ○ If the function is one of these special cases, the corresponding pointer (constructor, fallback, or
receive) is updated.
	4. Handling Regular Functions:
		○ If the function is not a special case:
			§ It's asserted that the function has a name (solAssert(!function->name().empty(), "");).
			§ The function is added to the functions map based on its name. This groups functions with the same name
together.
	5. Finding Duplicate Regular Functions:
Finally, the findDuplicateDefinitions(functions) function is called to specifically check for duplicate regular function
definitions. This function (not shown in the code snippet) would likely iterate over the functions map, and for each
group of functions with the same name, check if they have different parameter types. If functions with the same name and
parameters are found, they are considered duplicates, and errors would be reported.
*/

/**
 * @brief Checks for duplicate event definitions within a contract, including
 *        events inherited from base contracts.
 *
 * This function ensures that there are no events with the same name and
 * parameter types defined within the contract or inherited from its base
 * contracts.
 *
 * @param _contract A constant reference to the ContractDefinition AST node
 *                 representing the contract to be checked.
 */
void ContractLevelChecker::checkDuplicateEvents(ContractDefinition const& _contract)
{
	// 1. Initialize the 'events' map:
	//    - This map will store events grouped by their names. The keys are
	//      event names, and the values are vectors of `EventDefinition` pointers.
	std::map<std::string, std::vector<EventDefinition const*>> events;

	// 2. Iterate over base contracts:
	//    - Iterate through the linearized list of base contracts
	//      (including the current contract itself).
	for (auto const* contract: _contract.annotation().linearizedBaseContracts)
	{
		// 3. Iterate over events in each base contract:
		for (EventDefinition const* event: contract->events())
		{
			// Add the event to the 'events' map, using its name as the key.
			events[event->name()].push_back(event);
		}
	}

	// 4. Check for duplicate events (same name and parameters):
	//    - Call the `findDuplicateDefinitions` function (defined elsewhere) to
	//      identify and report any events with the same name and parameter list.
	findDuplicateDefinitions(events);
}
/*
Explanation:
	1. Initialization:
		○ A map named events is created to store events grouped by their names. This map is used to easily check for
events with the same name later.
	2. Iterating Through Base Contracts:
		○ The code iterates through the linearizedBaseContracts of the given _contract. This list includes the contract
itself and all its base contracts in the order they are inherited. This ensures that events from all levels of
inheritance are considered.
	3. Collecting Events:
		○ For each base contract, the code iterates through its defined events (contract->events()).
		○ Each event is added to the events map using its name as the key. If multiple events have the same name (from
different base contracts or within the same contract), they will be added to the same vector within the map.
	4. Checking for Duplicates:
		○ Finally, the findDuplicateDefinitions(events) function is called. This function (assumed to be defined
elsewhere) is responsible for checking for duplicate definitions within the provided map of events. It would likely: §
Iterate over the events map. § For each event name (key), examine the vector of EventDefinition pointers. § Compare the
parameter types of the events within each vector to determine if any duplicates exist (same name and parameters). If
duplicates are found, appropriate errors would be reported, likely using an ErrorReporter similar to the
checkDuplicateFunctions example.
*/

/**
 * @brief Performs checks on the receive ether function (if defined) within a contract.
 *
 * This function verifies that a receive ether function, if present, adheres to
 * the following rules:
 *  - It cannot be defined in a library.
 *  - It must have "payable" state mutability.
 *  - It must have "external" visibility.
 *  - It cannot have any return values.
 *  - It cannot take any parameters.
 *
 * @param _contract A constant reference to the ContractDefinition AST node representing
 *                 the contract to be checked.
 */
void ContractLevelChecker::checkReceiveFunction(ContractDefinition const& _contract)
{
	// 1. Iterate through defined functions in the contract:
	for (FunctionDefinition const* function: _contract.definedFunctions())
	{
		// 2. Assert that the 'function' pointer is not null:
		solAssert(function, ""); // This assertion ensures you have a valid function pointer.

		// 3. Check if the function is a receive ether function:
		if (function->isReceive())
		{
			// 4. Check if the function is defined within a library:
			if (function->libraryFunction())
			{
				m_errorReporter.declarationError(
					4549_error,										 // Error code for receive function in library
					function->location(),							 // Location of the receive function
					"Libraries cannot have receive ether functions." // Error message
				);
			}

			// 5. Check if the function is payable:
			if (function->stateMutability() != StateMutability::Payable)
			{
				m_errorReporter.declarationError(
					7793_error,
					function->location(),
					"Receive ether function must be payable, but is \""
						+ stateMutabilityToString(function->stateMutability()) + "\".");
			}

			// 6. Check if the function is external:
			if (function->visibility() != Visibility::External)
			{
				m_errorReporter.declarationError(
					4095_error, function->location(), "Receive ether function must be defined as \"external\".");
			}

			// 7. Check if the function has return values:
			if (!function->returnParameters().empty())
			{
				m_errorReporter.fatalDeclarationError( // 'fatalDeclarationError' might terminate compilation
					6899_error,
					function->returnParameterList()->location(), // Location of the return parameter list
					"Receive ether function cannot return values.");
			}

			// 8. Check if the function has parameters:
			if (!function->parameters().empty())
			{
				m_errorReporter.fatalDeclarationError(
					6857_error,
					function->parameterList().location(), // Location of the parameter list
					"Receive ether function cannot take parameters.");
			}
		}
	}
}

template<class T>
/**
 * @brief Finds and reports duplicate definitions within a map of definitions.
 *
 * This function is designed to detect duplicate function or event definitions
 * that have the same name and parameter types. It iterates through a map of
 * definitions, where keys are names (e.g., function/event names) and values
 * are vectors of definitions (e.g., `FunctionDefinition*` or `EventDefinition*`).
 *
 * @tparam T The type of definition (e.g., `FunctionDefinition const*` or
 *           `EventDefinition const*`).
 * @param _definitions A map of definitions, where the keys are names and
 *                     the values are vectors of definitions.
 */
void ContractLevelChecker::findDuplicateDefinitions(std::map<std::string, std::vector<T>> const& _definitions)
{
	// 1. Iterate through each named group of definitions:
	for (auto const& it: _definitions)
	{
		// 2. Get the vector of definitions (overloads) for the current name:
		std::vector<T> const& overloads = it.second;

		// 3. Use a set to keep track of reported indices (to avoid duplicate errors):
		std::set<size_t> reported;

		// 4. Iterate through the overloads:
		for (size_t i = 0; i < overloads.size() && !reported.count(i); ++i)
		{
			// Create a SecondarySourceLocation object to store information
			// about additional error locations (if any).
			SecondarySourceLocation ssl;

			// 5. Compare the current overload (i) with subsequent overloads (j):
			for (size_t j = i + 1; j < overloads.size(); ++j)
			{
				// 6. Check if two overloads have the same parameters:
				if (hasEqualExternalCallableParameters(*overloads[i], *overloads[j]))
				{
					// 7. Assertion to check if the definitions are in the expected scope:
					solAssert(
						(dynamic_cast<ContractDefinition const*>(overloads[i]->scope())
						 && dynamic_cast<ContractDefinition const*>(overloads[j]->scope())
						 && overloads[i]->name() == overloads[j]->name())
							|| (dynamic_cast<SourceUnit const*>(overloads[i]->scope())
								&& dynamic_cast<SourceUnit const*>(overloads[j]->scope())),
						"Override is neither a namesake function/event in contract scope nor "
						"a free function/event (alias).");

					// 8. Update the secondary source location with the location of
					//    the duplicate definition:
					ssl.append("Other declaration is here:", overloads[j]->location());

					// 9. Mark the index 'j' as reported:
					reported.insert(j);
				}
			}

			// 10. If any duplicates were found for the current overload (i):
			if (!ssl.infos.size())
				continue; // Skip error reporting if no duplicates

			// 11. Determine the appropriate error message and ID based on the
			//     definition type (function or event):
			ErrorId error;
			std::string message;
			if constexpr (std::is_same_v<T, FunctionDefinition const*>)
			{
				error = 1686_error; // Error code for duplicate function
				message = "Function with same name and parameter types defined twice.";
			}
			else
			{
				static_assert(
					std::is_same_v<T, EventDefinition const*>,
					"Expected \"FunctionDefinition const*\" or \"EventDefinition const*\"");
				error = 5883_error; // Error code for duplicate event
				message = "Event with same name and parameter types defined twice.";
			}

			// 12. Limit the size of the secondary source location message (if needed)
			//      and report the error:
			ssl.limitSize(message);
			m_errorReporter.declarationError(error, overloads[i]->location(), ssl, message);
		}
	}
}

/**
 * @brief Checks for unimplemented abstract functions, state variable getters,
 *        and modifiers within a contract.
 *
 * This function ensures that if a contract is marked as abstract or inherits
 * from abstract base contracts, all abstract members (functions, state variable
 * getters, and modifiers) are implemented. It also checks for incorrect usage
 * of the "abstract" keyword.
 *
 * @param _contract A constant reference to the ContractDefinition AST node representing
 *                 the contract to be checked.
 */
void ContractLevelChecker::checkAbstractDefinitions(ContractDefinition const& _contract)
{
	// 1. Define a set to track override proxies:
	//    - `OverrideProxy` (assumed to be defined elsewhere) is likely a helper
	//       class that helps track abstract members and their implementations.
	//    - The set uses a custom comparison function (`OverrideProxy::CompareBySignature`)
	//      to compare proxies based on signature.
	std::set<OverrideProxy, OverrideProxy::CompareBySignature> proxies;

	// 2. Define a lambda function to register an override proxy:
	//    - This lambda simplifies the process of adding or updating proxies
	//      in the 'proxies' set.
	auto registerProxy = [&proxies](OverrideProxy const& _overrideProxy)
	{
		// If the proxy already exists and is implemented, remove the old one.
		if (!_overrideProxy.unimplemented())
		{
			proxies.erase(_overrideProxy);
		}

		// Insert (or re-insert) the proxy into the set.
		proxies.insert(_overrideProxy);
	};

	// 3. Iterate through base contracts in reverse order (from most base to derived):
	//    - This ensures that derived class members overwrite base class members
	//      in the 'proxies' set if they are overriding them.
	for (ContractDefinition const* contract: _contract.annotation().linearizedBaseContracts | ranges::views::reverse)
	{
		// 4. Register external state variable getters as proxies:
		for (VariableDeclaration const* v: contract->stateVariables())
		{
			if (v->isPartOfExternalInterface())
			{
				registerProxy(OverrideProxy(v));
			}
		}

		// 5. Register non-constructor functions as proxies:
		for (FunctionDefinition const* function: contract->definedFunctions())
		{
			if (!function->isConstructor())
			{
				registerProxy(OverrideProxy(function));
			}
		}

		// 6. Register modifiers as proxies:
		for (ModifierDefinition const* modifier: contract->functionModifiers())
		{
			registerProxy(OverrideProxy(modifier));
		}
	}

	// 7. Update the 'unimplementedDeclarations' annotation:
	//    - Iterate through the collected proxies.
	for (auto const& proxy: proxies)
	{
		// If a proxy is unimplemented, add the corresponding declaration
		// to the 'unimplementedDeclarations' list in the contract's annotation.
		if (proxy.unimplemented())
		{
			_contract.annotation().unimplementedDeclarations->push_back(proxy.declaration());
		}
	}

	// 8. Check for incorrect usage of the "abstract" keyword:
	if (_contract.abstract())
	{ // If the contract is marked as 'abstract'...
		if (_contract.contractKind() == ContractKind::Interface)
		{
			// Interfaces are implicitly abstract, so the keyword is redundant.
			m_errorReporter.typeError(
				9348_error,
				_contract.location(),
				"Interfaces do not need the \"abstract\" keyword, they are abstract implicitly.");
		}
		else if (_contract.contractKind() == ContractKind::Library)
		{
			// Libraries cannot be abstract.
			m_errorReporter.typeError(9571_error, _contract.location(), "Libraries cannot be abstract.");
		}
		else
		{
			// If it's not an interface or library, it must be a regular contract.
			solAssert(_contract.contractKind() == ContractKind::Contract, "");
		}
	}

	// 9. Check for unimplemented abstract members in non-abstract contracts:
	//    - This check is skipped for libraries, as they are not inherited.
	if (_contract.contractKind() == ContractKind::Contract && !_contract.abstract()
		&& !_contract.annotation().unimplementedDeclarations->empty())
	{
		// Create a SecondarySourceLocation to accumulate locations of
		// unimplemented members.
		SecondarySourceLocation ssl;
		for (auto declaration: *_contract.annotation().unimplementedDeclarations)
		{
			ssl.append("Missing implementation: ", declaration->location());
		}

		// Report an error, indicating that the contract should be marked as 'abstract'.
		m_errorReporter.typeError(
			3656_error,
			_contract.location(),
			ssl,
			"Contract \"" + *_contract.annotation().canonicalName + "\" should be marked as abstract.");
	}
}
/*
Explanation:
	1. Override Proxy Setup: The code sets up a system to track abstract members (functions, state variable getters, and
modifiers) and whether they have been implemented. It uses a std::set of OverrideProxy objects (assumed to be defined
elsewhere) for this purpose. The set is ordered by function/modifier signature to facilitate comparisons.
	2. Base Contract Iteration: The code iterates through the contract's base contracts in reverse order of inheritance
(from most base to derived). This is crucial for correctly identifying overrides.
	3. Proxy Registration: For each base contract, the code registers external state variable getters, non-constructor
functions, and modifiers as potential overrides using registerProxy. The lambda function ensures that if an override is
encountered, it takes precedence over the base member in the proxies set.
	4. Unimplemented Member Tracking: After processing base contracts, the code iterates through the proxies set. If a
proxy is marked as unimplemented, it means the corresponding member is abstract and hasn't been implemented. These
unimplemented members are added to the contract's unimplementedDeclarations annotation.
	5. Abstract Keyword Validation: The code checks if the contract is marked as abstract. If it is:
		○ It ensures that the contract is not an interface (as interfaces are implicitly abstract).
		○ It makes sure that the contract is not a library (libraries cannot be abstract).
Unimplemented Member Error Reporting: For non-abstract contracts, the code checks if there are any unimplemented
members. If so, an error is reported, suggesting that the contract should be marked as abstract because it has
unimplemented abstract members. This error message includes the locations of all unimplemented members for easier
navigation.
*/


/**
 * @brief Checks the arguments passed to base contract constructors.
 *
 * This function performs two main tasks:
 *  1. It identifies and annotates the arguments used to call base
 *     contract constructors.
 *  2. It ensures that all required base constructors (those with parameters)
 *     have arguments provided. If not, it suggests marking the contract as
 *     'abstract'.
 *
 * @param _contract A constant reference to the ContractDefinition AST node representing
 *                 the contract being checked.
 */
void ContractLevelChecker::checkBaseConstructorArguments(ContractDefinition const& _contract)
{
	// 1. Get the linearized list of base contracts:
	std::vector<ContractDefinition const*> const& bases = _contract.annotation().linearizedBaseContracts;

	// 2. Determine and annotate base constructor arguments:
	//    - Iterate through each base contract in the inheritance hierarchy.
	for (ContractDefinition const* contract: bases)
	{
		// 2.1 Check for modifier-style base constructor calls:
		if (FunctionDefinition const* constructor = contract->constructor())
		{
			for (auto const& modifier: constructor->modifiers())
			{
				// Check if the modifier is actually a base contract constructor call:
				if (auto baseContract
					= dynamic_cast<ContractDefinition const*>(modifier->name().annotation().referencedDeclaration))
				{
					// 2.1.1 Handle base constructor calls with arguments:
					if (modifier->arguments() && baseContract->constructor())
					{
						annotateBaseConstructorArguments(_contract, baseContract->constructor(), modifier.get());
					}
					else if (modifier->arguments())
					{ // 2.1.2 Handle calls without arguments:
						m_errorReporter.declarationError(
							1563_error,
							modifier->location(),
							"Modifier-style base constructor call without arguments.");
					}
				}
			}
		}

		// 2.2 Check for inheritance specifier-style base constructor calls:
		for (ASTPointer<InheritanceSpecifier> const& base: contract->baseContracts())
		{
			ContractDefinition const* baseContract
				= dynamic_cast<ContractDefinition const*>(base->name().annotation().referencedDeclaration);
			solAssert(baseContract, ""); // Ensure the base contract is valid.

			if (baseContract->constructor() && base->arguments() && !base->arguments()->empty())
			{
				annotateBaseConstructorArguments(_contract, baseContract->constructor(), base.get());
			}
		}
	}

	// 3. Check for missing base constructor arguments:
	//    - This check is only performed for non-abstract contracts.
	if (_contract.contractKind() == ContractKind::Contract && !_contract.abstract())
	{
		for (ContractDefinition const* baseContract: bases)
		{
			if (FunctionDefinition const* baseConstructor = baseContract->constructor())
			{
				// Check if the base constructor has parameters and no arguments were provided:
				if (baseContract != &_contract && !baseConstructor->parameters().empty()
					&& _contract.annotation().baseConstructorArguments.count(baseConstructor) == 0)
				{
					m_errorReporter.typeError(
						3415_error,
						_contract.location(),
						SecondarySourceLocation{}
							.append("Base constructor parameters:", baseConstructor->parameterList().location()),
						fmt::format(
							"No arguments passed to the base constructor. Specify the arguments or mark \"{}\" as "
							"abstract.",
							*_contract.annotation().canonicalName));
				}
			}
		}
	}
}

/**
 * @brief Annotates the arguments used for a base contract constructor call.
 *
 * This function records the arguments passed to a base contract constructor
 * call in the annotations of the current contract. It ensures that arguments
 * for the same base constructor are not specified multiple times.
 *
 * @param _currentContract  A constant reference to the ContractDefinition of
 *                         the contract being analyzed.
 * @param _baseConstructor  A pointer to the FunctionDefinition representing the
 *                         base contract constructor being called.
 * @param _argumentNode    A pointer to the ASTNode representing the arguments
 *                         passed to the constructor (e.g., a FunctionCallArguments
 *                         node or an InheritanceSpecifier node).
 */
void ContractLevelChecker::annotateBaseConstructorArguments(
	ContractDefinition const& _currentContract,
	FunctionDefinition const* _baseConstructor,
	ASTNode const* _argumentNode)
{
	// 1. Assert valid input pointers:
	solAssert(_baseConstructor, ""); // Ensure the base constructor pointer is valid.
	solAssert(_argumentNode, "");	 // Ensure the argument node pointer is valid.

	// 2. Attempt to insert the base constructor and arguments into the annotation:
	//    - The annotation 'baseConstructorArguments' (likely a map) stores the
	//      base constructor as the key and the arguments node as the value.
	auto insertionResult = _currentContract.annotation().baseConstructorArguments.insert(
		std::make_pair(_baseConstructor, _argumentNode));

	// 3. Check for duplicate constructor call:
	//    - If the insertion was unsuccessful (insertionResult.second is false),
	//      it means the same base constructor has already been specified.
	if (!insertionResult.second)
	{
		// Get the previously stored argument node for the same base constructor.
		ASTNode const* previousNode = insertionResult.first->second;

		// Determine the main location (for the error message)
		// and secondary locations (for additional context).
		SourceLocation const* mainLocation = nullptr;
		SecondarySourceLocation ssl;

		// If the previous argument node or the current one are within the
		// contract's location, report the error at the previous node's location.
		if (_currentContract.location().contains(previousNode->location())
			|| _currentContract.location().contains(_argumentNode->location()))
		{
			mainLocation = &previousNode->location();
			ssl.append("Second constructor call is here:", _argumentNode->location());
		}
		else
		{
			// Otherwise, report at the contract's location.
			mainLocation = &_currentContract.location();
			ssl.append("First constructor call is here:", _argumentNode->location());
			ssl.append("Second constructor call is here:", previousNode->location());
		}

		// Report the error - duplicate base constructor arguments.
		m_errorReporter.declarationError(3364_error, *mainLocation, ssl, "Base constructor arguments given twice.");
	}
}
/*
Explanation:
	1. Input Validation: The function first uses solAssert to ensure that the provided pointers to the base constructor
(_baseConstructor) and the argument node (_argumentNode) are valid.
	2. Annotation Insertion:
		○ It attempts to insert a pair (base constructor pointer, argument node pointer) into the
baseConstructorArguments map in the current contract's annotation. This map tracks which arguments are passed to each
base constructor. ○ The insert function returns a std::pair. The second element of this pair indicates whether the
insertion was successful.
	3. Duplicate Argument Handling:
		○ If the insertion was unsuccessful (!insertionResult.second), it means that arguments for the same base
constructor have already been provided elsewhere. This is considered an error. ○ The code then determines the
appropriate source locations for the error message: § If the duplicate argument specification is within the current
contract's declaration, the error location is set to the location of the first occurrence of the argument specification.
			§ Otherwise, the error location is set to the contract's location, and secondary locations are added to
indicate where the duplicate arguments were specified. Finally, the declarationError function of the ErrorReporter is
used to report the "Base constructor arguments given twice" error, providing details about the duplicate locations.
*/

/**
 * @brief Checks for external function signature clashes in a contract and
 *        its base contracts.
 *
 * When functions or state variable getters (which implicitly define functions)
 * are part of the external interface of a contract, they are transformed into
 * a canonical "external" form. This function detects cases where two or more
 * functions, after this transformation, end up with the same external signature
 * (name and parameter types) but different return types or mutability.
 *
 * @param _contract A constant reference to the ContractDefinition representing
 *                 the contract to be checked.
 */
void ContractLevelChecker::checkExternalTypeClashes(ContractDefinition const& _contract)
{
	// 1. Create a map to store external function declarations:
	//    - The key is the function's external signature (a string), and the value
	//      is a vector of pairs. Each pair contains a pointer to the Declaration
	//      (FunctionDefinition or VariableDeclaration) and a FunctionTypePointer
	//      representing the function's type.
	std::map<std::string, std::vector<std::pair<Declaration const*, FunctionTypePointer>>> externalDeclarations;

	// 2. Iterate through the contract and its base contracts:
	for (ContractDefinition const* contract: _contract.annotation().linearizedBaseContracts)
	{
		// 3. Collect externally visible function definitions:
		for (FunctionDefinition const* f: contract->definedFunctions())
		{
			if (f->isPartOfExternalInterface())
			{
				// Get the function's type using the TypeProvider.
				auto functionType = TypeProvider::function(*f);

				// Check if the function has a valid interface function type.
				// This should be true under normal (non-error) conditions.
				if (functionType->interfaceFunctionType())
				{
					// Add the function to the 'externalDeclarations' map, using its
					// external signature as the key.
					externalDeclarations[functionType->externalSignature()]
						.emplace_back(f, functionType->asExternallyCallableFunction(false));
				}
			}
		}

		// 4. Collect externally visible state variable getters:
		for (VariableDeclaration const* v: contract->stateVariables())
		{
			// For each state variable 'v' in the current contract...
			if (v->isPartOfExternalInterface())
			{
				// If the state variable is part of the external interface
				// (e.g., it's 'public'), then it implicitly has a getter function.
				auto functionType = TypeProvider::function(*v);
				// Get the FunctionType representing the implicit getter function for the
				// state variable 'v' using the TypeProvider.

				// Check if the getter function has a valid interface function type.
				// This should be true unless there are other errors in the code.
				if (functionType->interfaceFunctionType())
				{
					// Add the state variable's implicit getter to the 'externalDeclarations' map.
					// The key is the external signature of the getter function.
					// We store the VariableDeclaration itself and its corresponding
					// external function type in the map.
					externalDeclarations[functionType->externalSignature()]
						.emplace_back(v, functionType->asExternallyCallableFunction(false));
				}
			}
		}
	}

	// 5. Check for signature clashes:
	//    - Iterate through each group of functions with the same external signature.
	for (auto const& [externalSignature, declarations]: externalDeclarations)
	{
		// Compare each declaration in the group with the others.
		for (size_t i = 0; i < declarations.size(); ++i)
		{
			for (size_t j = i + 1; j < declarations.size(); ++j)
			{
				// Check if the parameter types of the two declarations are different.
				if (!declarations[i].second->hasEqualParameterTypes(*declarations[j].second))
				{
					// Report a type error indicating an external function clash.
					m_errorReporter.typeError(
						9914_error,
						declarations[j].first->location(), // Location of the clashing declaration
						"Function overload clash during conversion to external types for arguments.");
				}
			}
		}
	}
}

/*
Explanation:
	1. External Declarations Map: The function creates a map called externalDeclarations to store declarations
(functions and state variable getters) that are part of the external interface, grouped by their external signature (a
string representing the function's name and parameter types).
	2. Iterate and Collect: It iterates through the contract and its base contracts, collecting:
		○ Function definitions marked as external or public.
		○ State variables with automatically generated getter functions that are considered part of the external
interface. ○ For each collected declaration, it obtains its function type (TypeProvider::function) and converts it to
its external callable form (asExternallyCallableFunction(false)). This normalized form is used for comparison.
	3. Check for Clashes: The code then iterates through the externalDeclarations map. For each group of declarations
with the same external signature, it compares their normalized parameter types: ○ If two declarations have different
parameter types (after normalization), it indicates a clash because they would be indistinguishable when called
externally. Error Reporting: When a clash is detected, a type error (9914_error) is reported, indicating the location of
the clashing declaration.
*/

/**
 * @brief Checks for hash collisions in the function selectors of a contract's interface.
 *
 * Each function signature (function name and parameter types) in Solidity is
 * assigned a 4-byte hash, often called a "function selector." This function
 * detects if two or more functions in a contract's interface have the same
 * selector hash, which would lead to ambiguity and incorrect function calls.
 *
 * @param _contract A constant reference to the ContractDefinition representing
 *                 the contract being checked.
 */
void ContractLevelChecker::checkHashCollisions(ContractDefinition const& _contract)
{
	// 1. Create a set to store unique function selector hashes.
	std::set<util::FixedHash<4>> hashes;

	// 2. Iterate through the contract's interface function list:
	for (auto const& [hash, function]: _contract.interfaceFunctionList())
	{
		// 3. Check if the hash already exists in the 'hashes' set:
		if (hashes.count(hash))
		{
			// If the hash is already present, it indicates a collision.
			// Report a fatal type error.
			m_errorReporter.fatalTypeError(
				1860_error,			  // Error code for hash collision
				_contract.location(), // Location of the contract
				std::string("Function signature hash collision for ")
					+ function->externalSignature() // Error message, including the colliding signature
			);
		}

		// 4. If no collision, add the hash to the 'hashes' set:
		hashes.insert(hash);
	}

	// If no collisions are found, the function completes without reporting errors.
}

/**
 * @brief Performs checks specific to library contracts in Solidity.
 *
 * This function verifies that the provided `_contract` (which should be
 * a library) adheres to the following library-specific rules in Solidity:
 *  1. Libraries cannot inherit from other contracts.
 *  2. Libraries can only have constant state variables.
 *
 * @param _contract A constant reference to the ContractDefinition representing
 *                 the contract to be checked.
 */
void ContractLevelChecker::checkLibraryRequirements(ContractDefinition const& _contract)
{
	// 1. If the contract is not a library, skip the checks:
	if (!_contract.isLibrary())
	{
		return;
	}

	// 2. Check if the library inherits from any other contracts:
	if (!_contract.baseContracts().empty())
	{
		// If the library has base contracts, report an error.
		m_errorReporter.typeError(
			9469_error,			  // Error code for library inheritance
			_contract.location(), // Location of the library definition
			"Library is not allowed to inherit.");
	}

	// 3. Check for non-constant state variables in the library:
	for (auto const& var: _contract.stateVariables())
	{
		// Iterate through each state variable declared in the library.
		if (!var->isConstant())
		{
			// If a state variable is not declared as 'constant', report an error.
			m_errorReporter.typeError(
				9957_error,		 // Error code for non-constant state variable in library
				var->location(), // Location of the non-constant state variable declaration
				"Library cannot have non-constant state variables");
		}
	}
}
/*
Explanation:
Library Check: The function first checks if the provided _contract is actually a library using !_contract.isLibrary().
If it's not a library, the function immediately returns, as the subsequent checks are only relevant to libraries.
Inheritance Restriction: Solidity prohibits libraries from inheriting from other contracts. The code enforces this by
checking if the library has any base contracts (!_contract.baseContracts().empty()). If base contracts are found, an
error is reported, specifying that libraries cannot inherit. Constant State Variable Enforcement: Solidity mandates that
state variables within a library must be declared as constant. The code enforces this by iterating through all the state
variables in the library: For each state variable (var), it checks if it is declared as constant using
!var->isConstant(). If a non-constant state variable is found, an error is reported.
*/

/**
 * @brief Checks for ABI compatibility issues when a contract inherits
 *        from contracts that use ABIEncoderV2.
 *
 * Solidity has two versions of its ABI encoder (ABIEncoderV1 and
 * ABIEncoderV2). ABIEncoderV2 supports a wider range of types. This
 * function ensures that if a contract inherits from a contract that
 * uses ABIEncoderV2 types, the inheriting contract also uses
 * ABIEncoderV2.
 *
 * @param _contract The ContractDefinition of the contract being checked.
 */
void ContractLevelChecker::checkBaseABICompatibility(ContractDefinition const& _contract)
{
	// 1. Check if the current contract uses ABIEncoderV2:
	if (*_contract.sourceUnit().annotation().useABICoderV2)
	{
		// If the current contract uses ABIEncoderV2, there's no need for further checks.
		return;
	}

	// 2. Special handling for libraries (libraries cannot inherit):
	if (_contract.isLibrary())
	{
		solAssert(
			_contract.baseContracts().empty() || m_errorReporter.hasErrors(), "Library is not allowed to inherit");
		return;
	}

	// 3. Prepare to collect error locations (if any):
	SecondarySourceLocation errors;

	// 4. Iterate through the contract's interface functions:
	//    - 'interfaceFunctionList' includes inherited functions.
	for (auto const& [hash, func]: _contract.interfaceFunctionList())
	{
		// 4.1. Assert that the function has a valid declaration:
		solAssert(func.second->hasDeclaration(), "Function has no declaration?!");

		// 4.2. Check if the function declaration uses ABIEncoderV2:
		if (!*func.second->declaration().sourceUnit().annotation().useABICoderV2)
		{
			// If the function's source unit doesn't use ABIEncoderV2, skip it.
			continue;
		}

		// 4.3. Get the location of the function declaration:
		auto const& currentLoc = func.second->declaration().location();

		// 4.4. Check if any parameter or return type requires ABIEncoderV2:
		for (Type const* paramType: func.second->parameterTypes() + func.second->returnParameterTypes())
		{
			if (!TypeChecker::typeSupportedByOldABIEncoder(*paramType, false))
			{
				// If a type is found that's not supported by the old encoder,
				// add its location to the 'errors' object.
				errors.append("Type only supported by ABIEncoderV2", currentLoc);
				break; // Move on to the next function if an incompatible type is found
			}
		}
	}

	// 5. Report error if any incompatible types were found:
	if (!errors.infos.empty())
	{
		m_errorReporter.fatalTypeError(
			6594_error,			  // Error code for ABI compatibility issue
			_contract.location(), // Location of the inheriting contract
			errors,				  // Secondary locations of problematic types
			std::string("Contract \"") + _contract.name()
				+ "\" does not use ABI coder v2 but wants to inherit from a contract "
				+ "which uses types that require it. "
				+ "Use \"pragma abicoder v2;\" for the inheriting contract as well to enable the feature.");
	}
}

/*
Explanation:
	1. ABIEncoderV2 Check: The function first checks if the current contract (_contract) uses ABIEncoderV2 by examining
its useABICoderV2 annotation. If it does, the function returns early, as there is no compatibility issue.
	2. Library Handling: It handles the special case of libraries. Libraries cannot inherit from other contracts, so if
_contract is a library, it includes an assertion to ensure this rule is followed.
	3. Error Collection: A SecondarySourceLocation object (errors) is created to store locations of potential ABI
compatibility issues that are encountered.
	4. Interface Function Iteration: The code iterates through the contract's interface functions, which include
inherited functions.
	5. ABIEncoderV2 Usage Check: For each function, it checks if the function's declaration originates from a source
unit that uses ABIEncoderV2. If it doesn't, the function is skipped.
	6. Parameter and Return Type Compatibility: If the function's declaration does use ABIEncoderV2, the code iterates
through its parameters and return types: ○ For each type (paramType), it checks if the type is supported by the older
ABIEncoderV1 using TypeChecker::typeSupportedByOldABIEncoder. ○ If a type is found that requires ABIEncoderV2, its
location is added to the errors object. Error Reporting: After checking all relevant functions, the code determines if
any incompatible types were found (!errors.infos.empty()). If so, it reports a fatal type error (6594_error), indicating
that the contract attempts to inherit from a contract using ABIEncoderV2 types without itself using ABIEncoderV2. It
also provides a helpful message suggesting the use of "pragma abicoder v2;".
*/

/**
 * @brief Checks if a contract has a payable fallback function
 *        without a receive ether function and emits a warning.
 *
 * In Solidity, a payable fallback function without a receive
 * ether function can lead to unexpected behavior when receiving
 * plain Ether transfers. This function is designed to detect this
 * potential issue and issue a warning to the developer.
 *
 * @param _contract A constant reference to the ContractDefinition AST node
 *                 representing the contract being checked.
 */
void ContractLevelChecker::checkPayableFallbackWithoutReceive(ContractDefinition const& _contract)
{
	// 1. Check if the contract has a fallback function:
	if (auto const* fallback = _contract.fallbackFunction())
	{
		// 2. If there is a fallback, check if it's payable and
		//    if the contract doesn't have a receive function:
		if (fallback->isPayable() && !_contract.interfaceFunctionList().empty() && !_contract.receiveFunction())
		{
			// 3. Issue a warning:
			m_errorReporter.warning(
				3628_error,			  // Warning error code
				_contract.location(), // Location of the contract
				"This contract has a payable fallback function, but no receive ether function. "
				"Consider adding a receive ether function.", // Warning message
				SecondarySourceLocation{}.append(
					"The payable fallback function is defined here.",
					fallback->location()) // Secondary location (fallback definition)
			);
		}
	}
}
/*
Explanation:
	1. Fallback Function Check: The function first checks if the contract has a fallback function defined using
_contract.fallbackFunction(). If there is no fallback function, there is no issue, so the function does nothing.
	2. Payable and Receive Function Check: If a fallback function exists:
		○ fallback->isPayable(): It checks if the fallback function is declared as payable, which means it can receive
Ether. ○ !_contract.interfaceFunctionList().empty(): It verifies if the contract has at least one function in its
interface. This condition is likely present to ensure that the contract is intended to interact with external calls and
that the absence of a receive function is not simply an oversight in a very basic contract. ○
!_contract.receiveFunction(): It confirms that the contract does not have a dedicated receive() function defined.
Warning Emission: If all the conditions in step 2 are true, it means the contract has a payable fallback function but no
explicit receive function. This situation could lead to unexpected behavior if the contract receives a plain Ether
transfer (with no data). In such cases, the fallback function would be called, potentially bypassing the intended logic
for receiving Ether. To address this, the code emits a warning message using the ErrorReporter (often used for both
errors and warnings).
*/

/**
 * @brief Checks the estimated storage size of a contract, considering
 *        its state variables and those inherited from base contracts.
 *
 * This function calculates an upper bound on the storage size required
 * by the contract and its base contracts. If the estimated size exceeds
 * the maximum allowed storage size (2^256 slots), it reports an error.
 *
 * @param _contract A constant reference to the ContractDefinition of the
 *                 contract being checked.
 */
void ContractLevelChecker::checkStorageSize(ContractDefinition const& _contract)
{
	// 1. Initialize 'size' to 0 - this variable will track the estimated size.
	bigint size = 0;

	// 2. Iterate through the linearized base contracts in reverse order:
	//    - This ensures that base contract variables are accounted for before
	//      derived contract variables.
	for (ContractDefinition const* contract: _contract.annotation().linearizedBaseContracts | ranges::views::reverse)
	{
		// 3. Iterate over state variables for each contract:
		for (VariableDeclaration const* variable: contract->stateVariables())
		{
			// 4. Skip constant or immutable variables:
			//    - These variables don't occupy storage slots at runtime.
			if (!(variable->isConstant() || variable->immutable()))
			{
				// 5. Add the variable's storage size upper bound to 'size':
				size += variable->annotation().type->storageSizeUpperBound();

				// 6. Check for storage size overflow:
				//    - If the estimated size exceeds 2^256, report an error
				//      and stop the calculation.
				if (size >= bigint(1) << 256)
				{
					m_errorReporter.typeError(
						7676_error,			  // Error code for excessive storage size
						_contract.location(), // Location of the contract
						"Contract requires too much storage.");
					return; // Exit the function after reporting the error
				}
			}
		}
	}
	// If no errors are encountered during the loop, the function completes
	// without reporting any issues.
}
/*
Explanation:
	1. Initialization: A bigint variable named size is initialized to 0. This variable will accumulate the estimated
storage size required by the contract.
	2. Base Contract Iteration: The code iterates through the linearized list of base contracts
(linearizedBaseContracts) in reverse order (from most base to derived). This order is essential to ensure that storage
slots inherited from base contracts are accounted for before considering variables declared in the current contract.
	3. State Variable Iteration: Within each base contract, the code iterates over its state variables (stateVariables).
	4. Skip Constant and Immutable Variables: Constant (isConstant()) and immutable (immutable()) variables are skipped.
These variables do not consume storage slots during runtime, as they are either compile-time constants or their values
are known upon deployment and cannot be changed afterward.
	5. Accumulate Storage Size: For non-constant and non-immutable state variables, the code retrieves an upper bound on
their storage size using variable->annotation().type->storageSizeUpperBound(). This upper bound likely accounts for
potential padding and alignment requirements of the variable's data type. The calculated size is then added to the size
variable. Storage Overflow Check: After processing each variable, the code checks if the accumulated size exceeds the
maximum allowed storage size in Solidity (2^256 slots). If it does, a typeError is reported indicating that the contract
requires too much storage. The function then returns early, as further calculation is unnecessary.
*/
