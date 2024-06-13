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
 * @author Christian <c@ethdev.com>
 * @date 2015
 * Evaluator for types of constant expressions.
 */

#pragma once

#include <libsolidity/ast/ASTVisitor.h>

#include <utility>

namespace solidity::langutil
{
class ErrorReporter;
}

namespace solidity::frontend
{

class TypeChecker;

/**
 * Small drop-in replacement for TypeChecker to evaluate simple expressions of integer constants.
 *
 * Note: This always use "checked arithmetic" in the sense that any over- or underflow
 * results in "unknown" value.
 */
// Forward declarations for ASTNode, BinaryOperation, UnaryOperation, Literal, Identifier,
// TupleExpression, Type, Token, ErrorReporter, and rational (presumably from a math library).
// ...

/**
 * @brief This class implements an AST visitor that performs constant evaluation
 *        on a subset of expressions.
 */
class ConstantEvaluator: private ASTConstVisitor
{
public:
	/**
	 * @brief Structure to hold a typed rational value, combining the value with its type information.
	 */
	struct TypedRational
	{
		Type const* type; ///< Pointer to the type of the rational value.
		rational value;	  ///< The rational value itself.
	};

	/**
	 * @brief Attempts to evaluate an Expression at compile time to a TypedRational value.
	 *
	 * @param _errorReporter  A reference to the error reporter for reporting any evaluation errors.
	 * @param _expr          A constant reference to the Expression to be evaluated.
	 * @return std::optional<TypedRational> An optional containing the evaluated TypedRational
	 *         value if evaluation was successful, otherwise std::nullopt.
	 */
	static std::optional<TypedRational> evaluate(langutil::ErrorReporter& _errorReporter, Expression const& _expr);

	/**
	 * @brief Performs arbitrary-precision evaluation of a binary operator.
	 *
	 * @param _operator The binary operator to evaluate.
	 * @param _left     The left-hand side operand of the binary operation.
	 * @param _right    The right-hand side operand of the binary operation.
	 * @return std::optional<rational> An optional containing the evaluated rational
	 *         result if successful, otherwise std::nullopt (e.g., division by zero).
	 */
	static std::optional<rational>
	evaluateBinaryOperator(Token _operator, rational const& _left, rational const& _right);

	/**
	 * @brief Performs arbitrary-precision evaluation of a unary operator.
	 *
	 * @param _operator The unary operator to evaluate.
	 * @param _input    The operand of the unary operation.
	 * @return std::optional<rational> An optional containing the evaluated rational result if successful,
	 *         otherwise std::nullopt (e.g., bitwise operation on a fractional value).
	 */
	static std::optional<rational> evaluateUnaryOperator(Token _operator, rational const& _input);

private:
	/**
	 * @brief Private constructor to force the use of the static `evaluate` function.
	 *
	 * @param _errorReporter A reference to the error reporter for reporting any evaluation errors.
	 */
	explicit ConstantEvaluator(langutil::ErrorReporter& _errorReporter): m_errorReporter(_errorReporter) {}

	/**
	 * @brief Attempts to evaluate an arbitrary ASTNode to a TypedRational value.
	 *
	 * @param _node The AST node to evaluate.
	 * @return std::optional<TypedRational> An optional containing the evaluated TypedRational
	 *         value if successful, otherwise std::nullopt.
	 */
	std::optional<TypedRational> evaluate(ASTNode const& _node);

	// Visitor overrides for specific AST node types:

	void endVisit(BinaryOperation const& _operation) override; ///< Handles the end of a binary operation node visit.
	void endVisit(UnaryOperation const& _operation) override;  ///< Handles the end of a unary operation node visit.
	void endVisit(Literal const& _literal) override;		   ///< Handles the end of a literal node visit.
	void endVisit(Identifier const& _identifier) override;	   ///< Handles the end of an identifier node visit.
	void endVisit(TupleExpression const& _tuple) override;	   ///< Handles the end of a tuple expression node visit.

	langutil::ErrorReporter& m_errorReporter; ///< Reference to the error reporter for error reporting.
	size_t m_depth = 0;						  ///< Current recursion depth during evaluation.
	/// Map to store the evaluated values of sub-expressions and variable declarations.
	std::map<ASTNode const*, std::optional<TypedRational>> m_values;
};

}
