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

#include <libsolidity/analysis/ConstantEvaluator.h>

#include <liblangutil/ErrorReporter.h>
#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/TypeProvider.h>

#include <limits>

using namespace solidity;
using namespace solidity::frontend;
using namespace solidity::langutil;

using TypedRational = ConstantEvaluator::TypedRational;

namespace
{

/// Check whether (_base ** _exp) fits into 4096 bits.
/*
Core Objective

This code is designed to determine if very large numbers, potentially exceeding the capacity of standard data types,
will fit within specific bit limitations when manipulated in certain ways. The focus is on the following operations:

Exponentiation (_base ** _exp): Raising one large number to the power of another.
Scaling by Powers of 2 (_mantissa * (2 ** _expBase2)): Multiplying a large number by a power of 2 (which is a common
operation in floating-point representations). The code wants to ensure that these operations produce results that can be
safely represented within a 4096-bit space. This is crucial for preventing overflows and maintaining accuracy in
calculations involving very large or very precise numbers.

Function 1: fitsPrecisionExp

Inputs:
_base: The base of the exponentiation operation.
_exp: The exponent of the exponentiation operation.
Logic:
Base Checks:
If the base is zero, the result will always be zero, so it fits.
Asserts that the base is positive (likely an assumption of the broader system).
Bit Calculations:
bitsMax: The maximum allowed bit size (4096).
mostSignificantBaseBit: The position of the highest '1' bit in the base's binary representation. This roughly indicates
how many bits the base needs to be represented. bitsNeeded: Estimates the number of bits needed to represent the result
of the exponentiation. It's a conservative estimate using the most significant bit plus one. Result: If bitsNeeded is
less than or equal to bitsMax, the result is likely to fit. Function 2: fitsPrecisionBase2

Inputs:
_mantissa: The number to be scaled.
_expBase2: The exponent (power of 2) to scale by.
Logic:
This function essentially delegates the task to another function called fitsPrecisionBaseX (not shown in your snippet),
which is a more generalized version likely handling scaling by powers of any base, not just 2. Key Points and
Assumptions

Libraries: The code relies on the boost::multiprecision library for handling large integers (bigint) and the
boost::multiprecision::msb function to find the most significant bit. Approximation: The calculation of bitsNeeded is an
approximation. In rare cases, it might overestimate the required bits slightly, leading to a false negative (the result
actually fits, but the function says it doesn't). However, it won't underestimate, ensuring safety. Domain-Specific:
This code is clearly tailored for a specific context where 4096-bit limitations are important, possibly in a
cryptographic or high-precision numerical computing application.
*/
bool fitsPrecisionExp(bigint const& _base, bigint const& _exp)
{
	if (_base == 0)
		return true;

	solAssert(_base > 0, "");

	std::size_t const bitsMax = 4096;

	std::size_t mostSignificantBaseBit = static_cast<std::size_t>(boost::multiprecision::msb(_base));
	if (mostSignificantBaseBit == 0) // _base == 1
		return true;
	if (mostSignificantBaseBit > bitsMax) // _base >= 2 ^ 4096
		return false;

	bigint bitsNeeded = _exp * (mostSignificantBaseBit + 1);

	return bitsNeeded <= bitsMax;
}

/// Checks whether _mantissa * (2 ** _expBase10) fits into 4096 bits.
std::optional<rational> ConstantEvaluator::evaluateBinaryOperator(
	Token _operator,
	rational const& _left,
	rational const& _right) bool fitsPrecisionBase2(bigint const& _mantissa, uint32_t _expBase2)
{
	return fitsPrecisionBaseX(_mantissa, 1.0, _expBase2);
}

}

std::optional<rational>
ConstantEvaluator::evaluateBinaryOperator(Token _operator, rational const& _left, rational const& _right)
/**
 * Evaluates binary operations based on the given operator and operands.
 *
 * @param _operator The operator to apply.
 * @param _left The left operand.
 * @param _right The right operand.
 *
 * @return An optional rational result of the binary operation if successful, otherwise std::nullopt.
 *
 * @throws None
 */

{
	bool fractional = _left.denominator() != 1 || _right.denominator() != 1;
	switch (_operator)
	{
	// bit operations will only be enabled for integers and fixed types that resemble integers
	case Token::BitOr:			 // Start a case block for the bitwise OR operator (Token::BitOr)
		if (fractional)			 // Check if the operation is being performed on fractional numbers
			return std::nullopt; // If fractional, return nullopt (indicating the operation is invalid)
		else					 // If not fractional, proceed with the bitwise OR operation
			return _left.numerator()
				   | _right.numerator(); // Perform bitwise OR on the numerators of the operands and return the result
		/*• case Token::BitOr: This line starts a case block within a switch statement. This section of code will only
execute if the current Token is Token::BitOr, signifying that a bitwise OR operation is being requested. • if
(fractional): This line checks a boolean variable called fractional. This variable likely indicates whether the current
operation involves fractional numbers or whole numbers. If fractional is true, it means we're dealing with fractions. •
return std::nullopt;: If the fractional flag is true, this line returns std::nullopt. This is a way to signal that the
bitwise OR operation is not valid or applicable for fractions. Returning nullopt indicates an error or the absence of a
meaningful result. • else: This line introduces an alternative code block that will execute if the if condition is
false. This means that the operation is being performed on whole numbers (not fractions). • return _left.numerator() |
_right.numerator();: This is the heart of the operation. It performs the bitwise OR operation: ○ _left.numerator():
Calls the numerator() method on the _left object, which likely represents a fraction. This retrieves the numerator of
the left operand. ○ _right.numerator(): Calls the numerator() method on the _right object, retrieving the numerator of
the right operand. ○ |: This is the bitwise OR operator. It performs a bit-by-bit OR comparison between the two
numerators, setting each bit in the result to 1 if either corresponding bit in the operands is 1. return ...: The result
of the bitwise OR operation is returned
*/
	case Token::BitXor:			 // Start a case block for the bitwise XOR operator (Token::BitXor)
		if (fractional)			 // Check if the operation is being performed on fractional numbers
			return std::nullopt; // If fractional, return nullopt (indicating the operation is invalid)
		else					 // If not fractional, proceed with the bitwise XOR operation
			return _left.numerator()
				   ^ _right.numerator(); // Perform bitwise XOR on the numerators of the operands and return the result

	case Token::BitAnd:			 // Start a case block for the bitwise AND operator (Token::BitAnd)
		if (fractional)			 // Check if the operation is being performed on fractional numbers
			return std::nullopt; // If fractional, return nullopt (indicating the operation is invalid)
		else					 // If not fractional, proceed with the bitwise AND operation
			return _left.numerator()
				   & _right.numerator(); // Perform bitwise AND on the numerators of the operands and return the result

	case Token::Add:		   // Start a case block for the addition operator (Token::Add)
		return _left + _right; // Perform addition on the operands and return the result

	case Token::Sub:		   // Start a case block for the subtraction operator (Token::Sub)
		return _left - _right; // Perform subtraction on the operands and return the result

	case Token::Mul:		   // Start a case block for the multiplication operator (Token::Mul)
		return _left * _right; // Perform multiplication on the operands and return the result

	case Token::Div:			   // Start a case block for the division operator (Token::Div)
		if (_right == rational(0)) // Check if the right operand is zero
			return std::nullopt;   // If zero, return nullopt (division by zero is invalid)
		else					   // If not zero, proceed with division
			return _left / _right; // Perform division on the operands and return the result

	case Token::Mod:			   // Start a case block for the modulo operator (Token::Mod)
		if (_right == rational(0)) // Check if the right operand is zero
			return std::nullopt;   // If zero, return nullopt (modulo by zero is invalid)
		else if (fractional)	   // If not zero, but dealing with fractions
		{
			rational tempValue = _left / _right; // Calculate the quotient of the operands
			return _left
				   - (tempValue.numerator() / tempValue.denominator()) * _right; // Calculate the modulo for fractions
		}
		else // If not zero and not fractional, proceed with modulo on whole numbers
			return _left.numerator()
				   % _right.numerator(); // Perform modulo on the numerators of the operands and return the result
		break;							 // Exit the `case` block
	case Token::Exp:					 // Start a case block for the exponentiation operator (Token::Exp)
	{									 // Start a new block scope for this case

		/*
		This code block handles the exponentiation operation (Token::Exp). It takes two operands:
			• _left: The base of the exponentiation.
			• _right: The exponent.
		Line-by-Line Explanation:
			1. case Token::Exp:: This line starts a case block within a switch statement. This code will only execute if
	the current Token is Token::Exp, indicating an exponentiation operation.
			2. {: This line starts a new block scope for this case.
			3. if (_right.denominator() != 1): This line checks if the right operand (_right) is not a whole number. The
	denominator() method likely returns the denominator of the right operand, which is assumed to be a rational number.
	If the denominator is not 1, the exponent is not a whole number, and the exponentiation operation is invalid.
			4. return std::nullopt;: If the exponent is not a whole number, this line returns std::nullopt, indicating
	an error.
			5. bigint const& exp = _right.numerator();: This line extracts the numerator of the right operand (which is
	now guaranteed to be a whole number) and stores it in a constant reference variable named exp of type bigint. The
	bigint type likely represents large integers.
			6. // x ** 0 = 1: This is a comment indicating the special case of raising any number to the power of 0,
	which always results in 1.
			7. // for 0, 1 and -1 the size of the exponent doesn't have to be restricted: This comment indicates that
	the size of the exponent doesn't need to be checked for bases 0, 1, or -1, as the results are trivial.
			8. if (exp == 0): This line checks if the exponent is 0.
			9. return 1;: If the exponent is 0, this line returns 1, following the rule that any number raised to the
	power of 0 equals 1.
			10. else if (_left == 0 || _left == 1): This line checks if the base is 0 or 1.
			11. return _left;: If the base is 0 or 1, this line returns the base itself, following the rules that 0^n =
	0 and 1^n = 1 for any exponent n.
			12. else if (_left == -1): This line checks if the base is -1.
			13. bigint isOdd = abs(exp) & bigint(1);: This line calculates whether the absolute value of the exponent is
	odd. It takes the absolute value of the exponent (abs(exp)), performs a bitwise AND operation with 1 (& bigint(1)),
	and stores the result in isOdd. This operation sets isOdd to 1 if the exponent is odd, and 0 if it's even.
			14. return 1 - 2 * isOdd.convert_to<int>();: This line returns the result of the exponentiation for a base
	of -1. It calculates 1 - 2 * isOdd, which results in 1 if isOdd is 0 (exponent is even) and -1 if isOdd is 1
	(exponent is odd).
			15. else: This block executes if the base is neither 0, 1, nor -1.
			16. if (abs(exp) > std::numeric_limits<uint32_t>::max()): This line checks if the absolute value of the
	exponent is too large to be represented as a 32-bit unsigned integer. std::numeric_limits<uint32_t>::max()
	represents the maximum value a 32-bit unsigned integer can hold.
			17. return std::nullopt;: If the exponent is too large, this line returns std::nullopt as the result would
	be too large to represent.
			18. uint32_t absExp = bigint(abs(exp)).convert_to<uint32_t>();: This line converts the absolute value of the
	exponent to a 32-bit unsigned integer (uint32_t) and stores it in absExp.
			19. if (!fitsPrecisionExp(abs(_left.numerator()), absExp) || !fitsPrecisionExp(abs(_left.denominator()),
	absExp)): This line checks if the numerator and denominator of the base, raised to the exponent, would fit within
	the desired precision. The fitsPrecisionExp function likely checks if the results of the exponentiation would be
	within a certain limit to avoid potential overflow or loss of precision.
			20. return std::nullopt;: If the exponentiation would result in an overflow or loss of precision, this line
	returns std::nullopt.
			21. static auto const optimizedPow = [](bigint const& _base, uint32_t _exponent) -> bigint: This line
	defines a lambda function named optimizedPow for efficient exponentiation. The lambda function takes a bigint value
	(_base) and a uint32_t value (_exponent) as input and returns a bigint.
			22. if (_base == 1): This line checks if the base of the lambda function is 1.
			23. return 1;: If the base is 1, this line returns 1, as 1 raised to any power is always 1.
			24. else if (_base == -1): This line checks if the base is -1.
			25. return 1 - 2 * static_cast<int>(_exponent & 1);: This line calculates the result for a base of -1. It
	uses a bitwise AND operation to determine if the exponent is odd or even and returns 1 if even and -1 if odd.
			26. else: This line handles the case where the base is neither 1 nor -1.
			27. return boost::multiprecision::pow(_base, _exponent);: This line calls the pow function from the
	boost::multiprecision library to perform the exponentiation for general cases.
			28. bigint numerator = optimizedPow(_left.numerator(), absExp);: This line calls the optimizedPow lambda
	function to calculate the numerator of the result by raising the numerator of the base to the absolute value of the
	exponent.
			29. bigint denominator = optimizedPow(_left.denominator(), absExp);: This line calls the optimizedPow lambda
	function to calculate the denominator of the result by raising the denominator of the base to the absolute value of
	the exponent.
			30. if (exp >= 0): This line checks if the exponent is non-negative.
			31. return makeRational(numerator, denominator);: If the exponent is non-negative, this line creates a new
	rational number using the makeRational function with the calculated numerator and denominator and returns it.
			32. else: This line handles the case where the exponent is negative.
			33. return makeRational(denominator, numerator);: If the exponent is negative, this line creates a new
	rational number by inverting the result, using the denominator as the numerator and the numerator as the
	denominator, and returns it.
			34. break;: This line exits the case block, preventing further execution of code in other case blocks.
	}: This line closes the block scope for this case.
		*/
		if (_right.denominator() != 1) // Check if the right operand is not a whole number
			return std::nullopt; // If not a whole number, return nullopt (exponentiation is not defined for fractional
								 // exponents)
		bigint const& exp = _right.numerator(); // Extract the exponent from the right operand (a whole number)

		// x ** 0 = 1
		// for 0, 1 and -1 the size of the exponent doesn't have to be restricted
		if (exp == 0)					   // If the exponent is zero
			return 1;					   // Return 1 (any number raised to the power of 0 is 1)
		else if (_left == 0 || _left == 1) // If the base is 0 or 1
			return _left;				   // Return the base (0^n = 0, 1^n = 1)
		else if (_left == -1)			   // If the base is -1
		{
			bigint isOdd = abs(exp) & bigint(1);	// Calculate if the absolute value of the exponent is odd
			return 1 - 2 * isOdd.convert_to<int>(); // Calculate the result: (-1)^n = 1 if n is even, -1 if n is odd
		}
		else // If the base is neither 0, 1, nor -1
		{
			if (abs(exp)
				> std::numeric_limits<uint32_t>::max()) // Check if the absolute value of the exponent is too large
				return std::nullopt; // If too large, return nullopt (the result would be too big to represent)

			uint32_t absExp = bigint(abs(exp)).convert_to<uint32_t>(); // Convert the absolute value of the exponent to
																	   // a 32-bit unsigned integer

			if (!fitsPrecisionExp(abs(_left.numerator()), absExp) // Check if the numerator raised to the exponent fits
																  // within the precision
				|| !fitsPrecisionExp(abs(_left.denominator()), absExp)) // Check if the denominator raised to the
																		// exponent fits within the precision
				return std::nullopt; // If either doesn't fit, return nullopt (the result would be too imprecise)

			static auto const optimizedPow
				= [](bigint const& _base,
					 uint32_t _exponent) -> bigint // Define a lambda function for efficient exponentiation
			{
				if (_base == 1)		  // If the base is 1
					return 1;		  // Return 1 (1^n = 1)
				else if (_base == -1) // If the base is -1
					return 1
						   - 2
								 * static_cast<int>(
									 _exponent & 1); // Calculate the result: (-1)^n = 1 if n is even, -1 if n is odd
				else								 // If the base is neither 1 nor -1
					return boost::multiprecision::pow(_base, _exponent); // Use boost::multiprecision::pow for general
																		 // exponentiation
			};

			bigint numerator = optimizedPow(_left.numerator(), absExp);		// Calculate the numerator of the result
			bigint denominator = optimizedPow(_left.denominator(), absExp); // Calculate the denominator of the result

			if (exp >= 0)									 // If the exponent is non-negative
				return makeRational(numerator, denominator); // Create a rational number with the calculated numerator
															 // and denominator
			else											 // If the exponent is negative
				// invert
				return makeRational(denominator, numerator); // Create a rational number with the denominator as
															 // numerator and numerator as denominator (inversion)
		}
		break; // Exit the `case` block
	}
	case Token::SHL:			 // Start a case block for the left shift operator (Token::SHL)
	{							 // Start a new block scope for this case
								 /*
								 Explanation:
									 This code handles the left shift operation (Token::SHL) for rational numbers. It performs the shift
							 operation on the numerator of the rational number while considering potential errors and precision limits.
								 Line-by-Line Explanation:
									 1. case Token::SHL:: This line starts a case block within a switch statement, specifically for the
							 Token::SHL case, which represents a left shift operation.
									 2. {: This line opens a new scope for the case block.
									 3. if (fractional): This line checks if the fractional flag is set, indicating that the operands are
							 fractional numbers.
									 4. return std::nullopt;: If the operands are fractional, the code returns std::nullopt, indicating an error.
							 Left shift is not defined for fractional numbers.
									 5. else if (_right < 0): This line checks if the right operand (_right), representing the shift amount, is
							 negative.
									 6. return std::nullopt;: If the shift amount is negative, the code returns std::nullopt, indicating an
							 error. Left shifting by a negative amount is invalid.
									 7. else if (_right > std::numeric_limits<uint32_t>::max()): This line checks if the right operand (shift
							 amount) is larger than the maximum value representable by a uint32_t.
									 8. return std::nullopt;: If the shift amount is too large, the code returns std::nullopt, as the result
							 would likely exceed the representable range.
									 9. if (_left.numerator() == 0): This line checks if the numerator of the left operand (_left.numerator()),
							 which is the value being shifted, is zero.
									 10. return 0;: If the numerator is zero, the result of the left shift will always be zero, so the code
							 returns 0.
									 11. else: This block executes if the numerator of the left operand is not zero.
									 12. uint32_t exponent = _right.numerator().convert_to<uint32_t>();: This line converts the numerator of the
							 right operand (shift amount) to a uint32_t and stores it in the exponent variable.
									 13. if (!fitsPrecisionBase2(abs(_left.numerator()), exponent)): This line checks if performing the left
							 shift would result in a value that exceeds the precision limits. The fitsPrecisionBase2 function likely checks if
							 shifting the absolute value of the numerator by exponent bits would still result in a value that can be represented
							 accurately.
									 14. return std::nullopt;: If the precision check fails, the code returns std::nullopt, indicating that the
							 result would be too large or imprecise to represent.
									 15. return _left.numerator() * boost::multiprecision::pow(bigint(2), exponent);: This line calculates the
							 result of the left shift. It multiplies the numerator of the left operand by 2 raised to the power of the shift
							 amount (exponent). It uses boost::multiprecision::pow to handle potentially large exponent values.
									 16. break;: This line exits the case block, preventing the code from falling through to the next case.
							 }: This line closes the scope for the case block.
								 */
		if (fractional)			 // Check if the operation is being performed on fractional numbers
			return std::nullopt; // If fractional, return nullopt (left shift is not defined for fractions)
		else if (_right < 0)	 // Check if the right operand (shift amount) is negative
			return std::nullopt; // If negative, return nullopt (left shift by a negative amount is invalid)
		else if (_right > std::numeric_limits<uint32_t>::max()) // Check if the shift amount is too large
			return std::nullopt; // If too large, return nullopt (the result would be too big to represent)

		if (_left.numerator() == 0) // Check if the left operand (value to shift) is zero
			return 0;				// If zero, return 0 (shifting zero always results in zero)
		else						// If the left operand is not zero
		{
			uint32_t exponent
				= _right.numerator().convert_to<uint32_t>(); // Convert the shift amount to a 32-bit unsigned integer
			if (!fitsPrecisionBase2(abs(_left.numerator()), exponent)) // Check if the result would fit within the
																	   // precision
				return std::nullopt; // If not, return nullopt (the result would be too imprecise)
			return _left.numerator()
				   * boost::multiprecision::pow(bigint(2), exponent); // Calculate the result: multiply the numerator by
																	  // 2 raised to the shift amount
		}
		break; // Exit the `case` block
	}
	// NOTE: we're using >> (SAR) to denote right shifting. The type of the LValue
	//       determines the resulting type and the type of shift (SAR or SHR).
	case Token::SAR:			 // Start a case block for the right arithmetic shift operator (Token::SAR)
	{							 // Start a new block scope for this case
								 /*
								 Explanation:
									 This code block handles the right arithmetic shift operator (Token::SAR) for rational numbers. Unlike a
								 logical right shift that fills the leftmost bits with zeros, an arithmetic right shift preserves the sign of the
								 operand, filling the leftmost bits with the sign bit (0 for positive, 1 for negative).
								 Line-by-Line Explanation:
									 1. case Token::SAR:: This line initiates a case block within a switch statement dedicated to handling the
								 Token::SAR operator, signifying a right arithmetic shift operation.
									 2. {: This line opens a new scope for the case block.
									 3. if (fractional): Checks if the operation involves fractions. As in previous cases, arithmetic shifts on
								 fractions are undefined.
									 4. return std::nullopt;: Returns std::nullopt if the operands are fractions, signaling an invalid operation.
									 5. else if (_right < 0): Checks if the shift amount (_right) is negative.
									 6. return std::nullopt;: Returns std::nullopt for negative shift amounts, as it's an invalid operation.
									 7. else if (_right > std::numeric_limits<uint32_t>::max()): Checks if the shift amount is too large to be
								 represented by a uint32_t.
									 8. return std::nullopt;: Returns std::nullopt if the shift amount is too large.
									 9. if (_left.numerator() == 0): Checks if the numerator of the left operand (value to shift) is zero.
									 10. return 0;: If the numerator is zero, the shift result is always zero, so it returns 0.
									 11. else: This block executes if the numerator is not zero.
									 12. uint32_t exponent = _right.numerator().convert_to<uint32_t>();: Converts the shift amount to a uint32_t
								 and stores it in exponent.
									 13. if (exponent > boost::multiprecision::msb(boost::multiprecision::abs(_left.numerator()))): This line
								 checks if the shift amount (exponent) is greater than the position of the most significant set bit (MSB) in the
								 absolute value of the numerator.						  ○ boost::multiprecision::abs: Calculates the absolute
								 value of the numerator.						  ○ boost::multiprecision::msb: Finds the position of the most significant set bit
								 (counting from 0).
									 14. return _left.numerator() < 0 ? -1 : 0;: If the shift amount is greater than the MSB, it means we are
								 shifting out all significant bits. The result will depend on the sign of the numerator:						  ○
								 If the numerator is						  negative, the result is -1 (all bits set after the shift).						  ○ If the
								 numerator is positive, the result is 0 (all						  bits become 0 after the shift).
									 15. else: This block executes if the shift amount is within the range of set bits.
									 16. if (_left.numerator() < 0): Handles the case of a negative numerator.
									 17. // ... (Comments explaining the arithmetic for rounding towards negative infinity):
										 These comments explain the logic behind the calculation for negative numerators to ensure that the
								 result is rounded towards negative infinity. It involves adding 1 before the division and subtracting 1 after to
								 achieve the correct rounding behavior.
									 18. return rational((_left.numerator() + 1) / boost::multiprecision::pow(bigint(2), exponent) - bigint(1),
								 1);: Calculates the result for a negative numerator, ensuring rounding towards negative infinity.
									 19. else: Handles the case of a positive numerator.
									 20. return rational(_left.numerator() / boost::multiprecision::pow(bigint(2), exponent), 1);: Calculates the
								 result for a positive numerator.
									 21. break;: Exits the case block.
									 22. }: Closes the scope for the case block.
								 */
		if (fractional)			 // Check if the operation is being performed on fractional numbers
			return std::nullopt; // If fractional, return nullopt (right arithmetic shift is not defined for fractions)
		else if (_right < 0)	 // Check if the right operand (shift amount) is negative
			return std::nullopt; // If negative, return nullopt (right shift by a negative amount is invalid)
		else if (_right > std::numeric_limits<uint32_t>::max()) // Check if the shift amount is too large
			return std::nullopt; // If too large, return nullopt (the result would be too big to represent)

		if (_left.numerator() == 0) // Check if the left operand (value to shift) is zero
			return 0;				// If zero, return 0 (shifting zero always results in zero)
		else						// If the left operand is not zero
		{
			uint32_t exponent
				= _right.numerator().convert_to<uint32_t>(); // Convert the shift amount to a 32-bit unsigned integer
			// Check if the shift amount is larger than the most significant set bit of the absolute value of the
			// numerator
			if (exponent > boost::multiprecision::msb(boost::multiprecision::abs(_left.numerator())))
				return _left.numerator() < 0 ? -1
											 : 0; // If so, return -1 if the numerator is negative, otherwise return 0
			else // If the shift amount is within the range of set bits in the numerator
			{
				if (_left.numerator() < 0) // If the numerator is negative
				{
					// Add 1 to the negative value before dividing to get a result that is strictly too large,
					// then subtract 1 afterwards to round towards negative infinity.
					// This is the same algorithm as used in ExpressionCompiler::appendShiftOperatorCode(...).
					// To see this note that for negative x, xor(x,all_ones) = (-x-1) and
					// therefore xor(div(xor(x,all_ones), exp(2, shift_amount)), all_ones) is
					// -(-x - 1) / 2^shift_amount - 1, which is the same as
					// (x + 1) / 2^shift_amount - 1.
					return rational(
						(_left.numerator() + 1) / boost::multiprecision::pow(bigint(2), exponent) - bigint(1), 1);
				}
				else // If the numerator is positive
					return rational(_left.numerator() / boost::multiprecision::pow(bigint(2), exponent), 1);
			}
		}
		break; // Exit the `case` block
	}
	default:
		return std::nullopt;
	}
}

/**
 * @brief Evaluates a unary operator applied to a rational number.
 *
 * This function evaluates a unary operator applied to a rational number and returns the result.
 * If the operation is not supported or results in an error, it returns `std::nullopt`.
 *
 * @param _operator The unary operator to evaluate.
 * @param _input The rational number to apply the operator to.
 * @return std::optional<rational> The result of the operation, or `std::nullopt` if the
 *         operation is not supported or results in an error.
 */
std::optional<rational> ConstantEvaluator::evaluateUnaryOperator(Token _operator, rational const& _input)
/*
Explanation of the Function and Comments:
The evaluateUnaryOperator function takes two arguments:
_operator: This is a Token value that represents the unary operator to be applied (e.g., bitwise NOT, unary minus).
_input: This is a rational number, passed by constant reference, representing the operand to which the unary operator
should be applied. The function returns a std::optional<rational>. This indicates that the function might: Return a
valid rational value if the operation is successful. Return std::nullopt if the operation is not supported for the given
operator or if an error occurs. Code Breakdown: switch (_operator): A switch statement is used to handle different unary
operator cases based on the value of _operator. case Token::BitNot:: This case handles the bitwise NOT (~) operator. It
first checks if the input rational number is actually a whole number (denominator is 1). If not, it returns std::nullopt
as bitwise NOT is not defined for fractions. If the input is a whole number, it returns the bitwise NOT of the numerator
using the ~ operator. case Token::Sub:: This case handles the unary minus (-) operator. It directly returns the negation
of the input rational number using the unary - operator. default:: If the _operator doesn't match any of the defined
cases, the function returns std::nullopt, indicating that the operator is not supported or an error has occurred. Key
Points: Error Handling: The function uses std::nullopt to gracefully handle cases where the operation is not valid
(e.g., bitwise NOT on fractions) or not supported. Operator Overloading: The code assumes that the rational class has
overloaded the unary - operator and the bitwise NOT (~) operator to work with rational numbers. Clarity: The comments
added to the code significantly enhance its readability by clearly explaining the purpose of the function, the
arguments, the return value, and the logic within each case of the switch statement. This makes the code easier to
understand and maintain.
*/
{
	switch (_operator)
	{
	case Token::BitNot:				   // Bitwise NOT operator
		if (_input.denominator() != 1) // Check if the input is a whole number
			return std::nullopt;	   // If not, return nullopt (bitwise NOT is not defined for fractions)
		else
			return ~_input.numerator(); // If so, return the bitwise NOT of the numerator

	case Token::Sub:	// Unary minus operator
		return -_input; // Return the negation of the input

	default:
		return std::nullopt; // For any other operator, return nullopt (not supported)
	}
}

namespace
{

/**
 * @brief Converts a rational number to a TypedRational with a specific type, if possible.
 *
 * This function attempts to convert a given rational number (`_value`) to a `TypedRational`
 * with a specified target type (`_type`). It handles conversions to both rational number
 * types and integer types. If the conversion is not possible due to type mismatch or
 * potential overflow, the function returns `std::nullopt`.
 *
 * @param _value The rational number to convert.
 * @param _type The target type to convert the rational number to.
 * @return std::optional<TypedRational> The converted TypedRational,
 *         or `std::nullopt` if the conversion is not possible.
 */
std::optional<TypedRational> convertType(rational const& _value, Type const& _type)
/*
Explanation and Example:
The convertType function aims to safely convert a rational number (_value) into a TypedRational with a specific target
type (_type). It handles these main scenarios:
1. Target Type is a Rational Number:
if (_type.category() == Type::Category::RationalNumber): This checks if the target type's category is "RationalNumber"
(e.g., another rational number type with potentially different precision). return
TypedRational{TypeProvider::rationalNumber(_value), _value};: If the target type is also a rational number, the
conversion is straightforward. This line constructs a TypedRational by: Obtaining the appropriate rational number type
from TypeProvider based on the input value (_value). Using the original rational number value (_value) for the
TypedRational.
2. Target Type is an Integer:
else if (auto const* integerType = dynamic_cast<IntegerType const*>(&_type)): This part checks if the target type is an
integer type using dynamic_cast. If the cast is successful, it means _type is indeed a pointer to an IntegerType, and
the pointer is stored in the integerType variable. if (_value > integerType->maxValue() || _value <
integerType->minValue()): This checks for potential overflow. It ensures that the rational number's value is within the
bounds of the target integer type (using maxValue() and minValue() methods of the IntegerType). return std::nullopt;: If
an overflow is detected, the function returns std::nullopt, indicating that a safe conversion is not possible. else
return TypedRational{&_type, _value.numerator() / _value.denominator()};: If the value is within bounds, this line
creates a TypedRational: It uses the _type (now known to be an integer type) for the TypedRational. It performs integer
division (_value.numerator() / _value.denominator()) to get the integer part of the rational number and uses that as the
value.
3. Other Target Types:
else return std::nullopt;: If the target type is neither a rational number type nor an integer type, the function
returns std::nullopt indicating the conversion is not supported. Example: rational value{5, 2}; // Represents the
rational number 5/2 (2.5)

Type rationalType = ...; // Assume this represents a rational number type
Type int32Type = ...;    // Assume this represents a 32-bit integer type

// Conversion to a rational type should succeed
std::optional<TypedRational> typedRational = convertType(value, rationalType);
// typedRational will contain a TypedRational with the value 5/2 and the type rationalType

// Conversion to an integer type might fail due to overflow
std::optional<TypedRational> typedInt32 = convertType(value, int32Type);
// If int32Type can represent 2, typedInt32 will contain a TypedRational with value 2.
// If int32Type cannot represent 2 (e.g., it's an unsigned integer type), typedInt32 will be nullopt.
*/
{
	if (_type.category() == Type::Category::RationalNumber) // Check if the target type is a rational number type
		return TypedRational{TypeProvider::rationalNumber(_value), _value}; // Construct and return a TypedRational with
																			// the target type and the input value
	else if (auto const* integerType = dynamic_cast<IntegerType const*>(&_type)) // Check if the target type is an
																				 // integer type
	{
		// Check if the value is within the bounds of the target integer type
		if (_value > integerType->maxValue() || _value < integerType->minValue())
			return std::nullopt; // Return nullopt if the value is out of bounds (potential overflow)
		else
			// If within bounds, construct and return a TypedRational with the target type and the integer part of the
			// value
			return TypedRational{&_type, _value.numerator() / _value.denominator()};
	}
	else
		return std::nullopt; // Return nullopt if the target type is neither rational nor integer
}

/**
 * @brief Converts a TypedRational to a new TypedRational with a different type, if possible.
 *
 * This function attempts to convert an optional TypedRational value (`_value`) to a new
 * TypedRational with a specified target type (`_type`). If the input `_value` is not empty
 * (contains a TypedRational), it delegates the conversion to the other `convertType`
 * function (which handles the actual type conversion). If the input `_value` is empty,
 * this function returns `std::nullopt` without attempting any conversion.
 *
 * @param _value The optional TypedRational value to convert.
 * @param _type The target type to convert the TypedRational to.
 * @return std::optional<TypedRational> The converted TypedRational (if successful), or
 *         `std::nullopt` if the input is empty or the conversion is not possible.
 */
std::optional<TypedRational> convertType(std::optional<TypedRational> const& _value, Type const& _type)
/*
Explanation and Example:
This convertType function is a convenient overload for working with optional TypedRational values. It simplifies the
process of converting a TypedRational, which might not have a value (i.e., be empty), to a potentially different type.
Line-by-Line Explanation:
return _value ? convertType(_value->value, _type) : std::nullopt;: This line contains the entire logic of the function
in a concise ternary operator expression. Let's break it down: _value ? : This part checks if the input _value (which is
an std::optional<TypedRational>) contains a value. It's equivalent to if (_value.has_value()).
convertType(_value->value, _type) : If _value has a value, this part is executed. It calls the other convertType
function overload (explained in the previous response), passing: _value->value: The actual rational value stored within
the input TypedRational. _type: The target type to convert to. : std::nullopt : If _value is empty (doesn't contain a
TypedRational), this part is executed, immediately returning std::nullopt without attempting any conversion. Example:
std::optional<TypedRational> maybeRational1 = ...; // Could contain a TypedRational or be empty
std::optional<TypedRational> maybeRational2 = TypedRational{..., rational{3, 4}};
Type targetType = ...; // Some target type

// Conversion from maybeRational1 - might be nullopt or contain a converted value
std::optional<TypedRational> result1 = convertType(maybeRational1, targetType);

// Conversion from maybeRational2 - will attempt conversion of the rational value 3/4
std::optional<TypedRational> result2 = convertType(maybeRational2, targetType);
*/
{
	return _value ? convertType(_value->value, _type) : std::nullopt;
}

/**
 * @brief Converts a constant value from a RationalNumberType to a TypedRational.
 *
 * This function attempts to create a TypedRational from a constant value associated
 * with a specific RationalNumberType. It's useful for handling cases where a type
 * directly represents a constant rational value. If the input type is not a
 * RationalNumberType, the function returns `std::nullopt`.
 *
 * @param _type The type (expected to be a RationalNumberType) containing the constant value.
 * @return std::optional<TypedRational> A TypedRational containing the constant value
 *         and the input type, or `std::nullopt` if the type is not a RationalNumberType.
 */
std::optional<TypedRational> constantToTypedValue(Type const& _type)
/*
Explanation and Example:
The constantToTypedValue function is designed to handle situations where a Type object itself represents a constant
rational number. For example, you might have a RationalNumberType that always represents the value "Pi" (π). This
function extracts that constant value and creates a TypedRational from it. Line-by-Line Breakdown: if (_type.category()
== Type::Category::RationalNumber): This line checks if the input _type belongs to the category "RationalNumber". This
assumes that your type system has a way to categorize types (e.g., integer, rational, etc.). return
TypedRational{&_type, dynamic_cast<RationalNumberType const&>(_type).value()};: If the type is indeed a
RationalNumberType, this line does the following: dynamic_cast<RationalNumberType const&>(_type): It performs a
dynamic_cast to safely cast the _type reference to a RationalNumberType reference. This assumes that RationalNumberType
is a specific type in your system that inherits from or is related to the more general Type.
**.value(): It calls a hypothetical value() method on the RationalNumberType object. This method is expected to return
the actual rational value represented by this type (e.g., the value of Pi). TypedRational{&_type, ...}: Finally, it
constructs a TypedRational object using:
&_type: A pointer to the input _type (now confirmed to be a RationalNumberType)
The rational value returned by _type.value().
else return std::nullopt;: If the input type is not a RationalNumberType, the function returns std::nullopt, indicating
that it cannot extract a constant rational value. Example: class RationalNumberType : public Type { public:
	// ... other methods ...

	rational value() const { return value_; } // Returns the constant rational value

private:
	rational value_;
};

// ...

RationalNumberType piType{rational{314159, 100000}}; // A type representing Pi (approximately)
Type someOtherType = ...; // Some other type

// Converting piType should succeed:
std::optional<TypedRational> typedPi = constantToTypedValue(piType);
// typedPi will contain a TypedRational with value ~3.14159 and type &piType.

// Converting someOtherType will fail:
std::optional<TypedRational> result = constantToTypedValue(someOtherType);
// result will be nullopt.
*/
{
	if (_type.category() == Type::Category::RationalNumber) // Check if the input type is a RationalNumberType
	{
		// Cast the type to RationalNumberType and extract its constant value
		return TypedRational{&_type, dynamic_cast<RationalNumberType const&>(_type).value()};
	}
	else
		return std::nullopt; // Return nullopt if the type is not a RationalNumberType
}

}

std::optional<TypedRational>
ConstantEvaluator::evaluate(langutil::ErrorReporter& _errorReporter, Expression const& _expr)
{
	return ConstantEvaluator{_errorReporter}.evaluate(_expr);
}


/**
 * @brief Evaluates a constant expression and returns its TypedRational value, if possible.
 *
 * This function evaluates a constant expression represented by an ASTNode.
 * It handles variable declarations and general expressions, caching results to
 * prevent redundant evaluations. If the expression cannot be evaluated to a
 * constant TypedRational value (e.g., contains non-constant variables or
 * unsupported operations), the function returns `std::nullopt`. It also detects
 * cyclic dependencies in constant definitions and reports a fatal error if found.
 *
 * @param _node The ASTNode representing the constant expression to evaluate.
 * @return std::optional<TypedRational> The evaluated TypedRational value, or
 *         `std::nullopt` if the expression cannot be evaluated to a constant.
 */
std::optional<TypedRational> ConstantEvaluator::evaluate(ASTNode const& _node)
/*
Explanation and Example:
The evaluate function acts as a recursive evaluator for constant expressions represented in an Abstract Syntax Tree
(AST). It takes an ASTNode as input and tries to determine its constant value, represented as a TypedRational.
Line-by-Line Breakdown:
	1. if (!m_values.count(&_node)): This line checks if the expression represented by _node has already been evaluated
and its value cached in the m_values map (presumably a member of ConstantEvaluator). If the value is cached, it skips
re-evaluation.
	2. if (auto const* varDecl = dynamic_cast<VariableDeclaration const*>(&_node)): This part handles the case where the
_node is a variable declaration: ○ It attempts to dynamic_cast the _node to a VariableDeclaration. ○ If successful, it
means this node represents a variable declaration.
	3. solAssert(varDecl->isConstant(), "");: This line asserts that the variable being declared is actually a constant.
If the variable is not a constant, this assertion will likely trigger an error (the behavior of solAssert is not shown
here but is assumed to be an assertion mechanism).
	4. if (!varDecl->value() || !varDecl->type()) ... else ...: This section handles cases where the variable
declaration might not have a value or type assigned yet: ○ If either is missing, the value is set to std::nullopt. ○ If
both are available, the function proceeds with evaluation: § m_depth++;: Increments a recursion depth counter, likely to
detect cyclic dependencies. § if (m_depth > 32) ...: Checks if the recursion depth exceeds a limit (32 in this case),
and if so, reports a fatal error indicating a potential cyclic definition. § m_values[&_node] =
convertType(evaluate(*varDecl->value()), *varDecl->type());: This is the core of the evaluation: □ It recursively calls
evaluate to evaluate the expression assigned to the variable (varDecl->value()). □ It converts the result of the
evaluation to the target type of the variable (varDecl->type()) using the convertType function. □ The final
TypedRational result is cached in m_values. § m_depth--;: Decrements the recursion depth counter.
	5. else if (auto const* expression = dynamic_cast<Expression const*>(&_node)): This else if branch handles cases
where the _node is a general expression (not just a variable declaration): ○ It tries to dynamic_cast the _node to an
Expression. ○ expression->accept(*this);: This is a key part of a Visitor pattern. It calls the accept method of the
Expression, passing *this (likely the ConstantEvaluator instance) as an argument. This will internally call a specific
visit method within ConstantEvaluator based on the actual type of the Expression. ○ if (!m_values.count(&_node))
m_values[&_node] = std::nullopt;: After visiting the expression, it checks if a value has been stored in m_values. If
not, it sets it to std::nullopt. This likely handles cases where the visit method for the specific Expression type
doesn't set a value (e.g., for unsupported operations).
	6. return m_values.at(&_node);: Finally, the function returns the evaluated and cached TypedRational value for the
given _node from the m_values map. Example: Let's say you have the following constant declarations in your code: const
int a = 5; const int b = 10; const int c = a + b; content_copyUse code with caution. The AST might look something like
this: VariableDeclaration (c)
	   |
	   +--- Expression (+)
			  |
			  +--- VariableReference (a)
			  |
			  +--- VariableReference (b)
content_copyUse code with caution.
When you call evaluate with the ASTNode representing the declaration of c:
	• The function recursively evaluates the expressions for a and b (which will result in TypedRational values 5 and
10). • It then evaluates the + expression, adding the values of a and b. • The final result (15) is converted to the
type of c (int) and stored in the cache. Key Points: • Caching: The function uses caching (m_values) to avoid redundant
evaluations of the same expressions. • Visitor Pattern: It utilizes the Visitor pattern to handle different expression
types (via the accept method and likely corresponding visit methods in ConstantEvaluator). • Error Handling: The
function checks for potential cyclic dependencies in constant definitions and reports an error if found. • Type Safety:
It uses the convertType function to ensure type safety during evaluation and assignment.

From <https://aistudio.google.com/app/prompts/new_chat>

*/
{
	if (!m_values.count(&_node)) // Check if the expression has been previously evaluated and cached
	{
		if (auto const* varDecl = dynamic_cast<VariableDeclaration const*>(&_node))
		{										  // If the node is a variable declaration:
			solAssert(varDecl->isConstant(), ""); // Verify that the variable is declared as constant
			// Handle cases where the variable's type or value is not yet available
			if (!varDecl->value() || !varDecl->type())
				m_values[&_node] = std::nullopt;
			else
			{
				m_depth++;		  // Increment recursion depth counter
				if (m_depth > 32) // Check for potential cyclic dependencies or excessive recursion
					// Report a fatal error if a cycle is detected
					m_errorReporter.fatalTypeError(
						5210_error,
						varDecl->location(),
						"Cyclic constant definition (or maximum recursion depth exhausted).");

				// Recursively evaluate the variable's initializer expression
				m_values[&_node] = convertType(evaluate(*varDecl->value()), *varDecl->type());
				m_depth--; // Decrement recursion depth counter
			}
		}
		else if (auto const* expression = dynamic_cast<Expression const*>(&_node))
		{							   // If the node is a general expression:
			expression->accept(*this); // Call the appropriate visit method based on the expression type
			// If the expression evaluation didn't set a value, default to nullopt
			if (!m_values.count(&_node))
				m_values[&_node] = std::nullopt;
		}
	}
	// Return the cached result
	return m_values.at(&_node);
}

/**
 * @brief Evaluates a unary operation during constant expression evaluation.
 *
 * This function is part of the Visitor pattern and is called when encountering a
 * UnaryOperation node in the AST during constant expression evaluation. It retrieves
 * the evaluated value of the subexpression, determines the result type of the unary
 * operation, performs the unary operation, and stores the final TypedRational result
 * in the expression value cache.
 *
 * @param _operation The UnaryOperation AST node being visited.
 */
void ConstantEvaluator::endVisit(UnaryOperation const& _operation)
/*
Explanation and Example:
The endVisit(UnaryOperation const& _operation) function is a critical part of the Visitor pattern implementation within
your ConstantEvaluator class. It defines the logic for evaluating unary operations encountered during constant
expression evaluation. How it Works:
	1. Evaluate Subexpression: It starts by recursively evaluating the subexpression associated with the unary operation
using evaluate(_operation.subExpression()). The result, if successful, is a TypedRational stored in the value variable.
If the subexpression doesn't evaluate successfully, the function returns early.
	2. Determine Result Type: It then determines the expected result type of the unary operation. This is done by
querying the type of the evaluated subexpression (value->type) using a method like unaryOperatorResult() and passing the
unary operator (_operation.getOperator()). This method likely uses type rules to determine the appropriate result type.
For example, the bitwise NOT operator (~) applied to a uint32_t would also likely result in a uint32_t.
	3. Convert to Result Type: Before performing the operation, it attempts to convert the evaluated subexpression
(value) to the determined result type (resultType) using the convertType function. This ensures type compatibility for
the operation.
	4. Perform Unary Operation: If the type conversion is successful, the function proceeds to perform the actual unary
operation using evaluateUnaryOperator. This function likely handles the specific logic for different unary operators
like bitwise NOT (~), unary minus (-), etc. The result of this operation is a raw rational value.
	5. Convert to TypedRational: The raw rational result is then converted into a TypedRational with the correct result
type (resultType) using convertType.
	6. Cache Result: Finally, the successfully evaluated TypedRational result is stored in the m_values cache (likely a
map) using the address of the _operation node as the key. Example: Let's say you have the following code: const uint32_t
x = 25; const uint32_t y = ~x; content_copyUse code with caution. When evaluating the expression for y:
	1. The endVisit function will be called for the ~ unary operation node.
	2. It first evaluates the subexpression (x), resulting in a TypedRational with the value 25 and a uint32_t type.
	3. The result type of the ~ operator on a uint32_t is also determined to be uint32_t.
	4. The evaluateUnaryOperator function performs the bitwise NOT on 25, resulting in a rational value.
	5. This rational result is then converted to a TypedRational with the uint32_t type.
	6. Finally, the TypedRational representing ~x is cached.
Key Points:
	• Visitor Pattern: This function is a core component of the Visitor pattern, enabling specific actions to be
performed for different AST node types. • Type Safety: The code emphasizes type safety by determining the correct result
type for the unary operation and performing necessary type conversions. • Error Handling: It handles potential errors
during subexpression evaluation, type conversion, and the final operation, typically returning early if an error occurs.
Caching: The evaluated result is cached to avoid redundant computations.
*/
{
	// Step 1: Evaluate the subexpression
	std::optional<TypedRational> value
		= evaluate(_operation.subExpression()); // Recursively evaluate the operand of the unary operation
	if (!value) // If subexpression evaluation fails (returns nullopt), stop further processing
		return;

	// Step 2: Determine the result type of the unary operation
	Type const* resultType = value->type->unaryOperatorResult(_operation.getOperator());
	//  ^ Get the result type of the unary operation from the subexpression's type
	if (!resultType) // If the result type is not defined (null), stop further processing
		return;

	// Step 3: Attempt to convert the subexpression value to the result type
	value = convertType(value, *resultType); // Try to convert the subexpression value to the expected result type
	if (!value)								 // If the conversion fails (returns nullopt), stop further processing
		return;

	// Step 4: Perform the unary operation
	// Evaluate the unary operation on the converted value (now of the correct result type)
	if (std::optional<rational> result = evaluateUnaryOperator(_operation.getOperator(), value->value))
	{
		// Step 5: Convert the result to the final TypedRational value
		// Attempt to convert the raw result to a TypedRational with the result type
		std::optional<TypedRational> convertedValue = convertType(*result, *resultType);
		if (!convertedValue)
			// If final conversion fails, report a fatal type error (likely an arithmetic issue)
			m_errorReporter
				.fatalTypeError(3667_error, _operation.location(), "Arithmetic error when computing constant value.");

		// Step 6: Store the result in the cache
		m_values[&_operation] = convertedValue; // Cache the evaluated TypedRational result
	}
}


/**
 * @brief Evaluates a binary operation during constant expression evaluation.
 *
 * This function, part of the Visitor pattern, is invoked when a BinaryOperation node
 * is encountered in the AST. It evaluates both the left and right operands,
 * determines the result type, performs the binary operation, and caches the
 * resulting TypedRational value. It handles type compatibility checks and reports
 * errors for unsupported type combinations or arithmetic errors.
 *
 * @param _operation The BinaryOperation AST node being visited.
 */
void ConstantEvaluator::endVisit(BinaryOperation const& _operation)
/*
Explanation and Example:
The endVisit(BinaryOperation const& _operation) function is analogous to the unary version but handles binary
operations. It follows these main steps:
	1. Evaluate Operands: Recursively evaluates both the left and right expressions of the binary operation using
evaluate(...). The results, if successful, are TypedRational values stored in left and right.
	2. Handle Comparison Operators (TODO): There's a placeholder comment indicating that comparison operators (<, >, ==,
etc.) might need special handling in the future. This is because comparison operators often return boolean values, even
if the operands are not boolean.
	3. Determine Result Type: The function determines the result type of the binary operation based on the operator
itself and the types of the evaluated operands. This is done using left->type->binaryOperatorResult(...), which likely
refers to a type system that defines type compatibility and result types for different operator combinations.
	4. Convert to Result Type: It attempts to convert both operands (left and right) to the determined result type using
convertType. This ensures type compatibility for the binary operation.
	5. Perform Binary Operation: If both operands are successfully converted, the function performs the actual binary
operation using evaluateBinaryOperator. The specific logic for each operator (e.g., +, -, *, /) is likely handled within
evaluateBinaryOperator.
	6. Convert to TypedRational: The raw rational result from the binary operation is converted to a TypedRational with
the correct resultType, again using convertType.
	7. Cache Result: Finally, the successfully evaluated and converted TypedRational value is cached in the m_values map
using the address of the _operation node as the key. Example: Consider the following code: const int x = 10; const int y
= 5; const int z = x + y;

*/
{
	// Step 1: Evaluate both operands of the binary operation
	std::optional<TypedRational> left = evaluate(_operation.leftExpression());	 // Evaluate the left operand
	std::optional<TypedRational> right = evaluate(_operation.rightExpression()); // Evaluate the right operand

	// If either operand evaluation fails, stop further processing
	if (!left || !right)
		return;

	// Step 2: Handle special case for comparison operators (if needed)
	// TODO (if comparison operators need special handling in the future):
	// Comparison operators might have a non-boolean result type, but we want a boolean result.
	if (TokenTraits::isCompareOp(_operation.getOperator()))
		return;

	// Step 3: Determine the result type of the operation
	// Get the result type based on the operator and operand types
	Type const* resultType = left->type->binaryOperatorResult(_operation.getOperator(), right->type);
	if (!resultType)
	{
		// If no valid result type is found (incompatible types), report a fatal type error
		m_errorReporter.fatalTypeError(
			6020_error,
			_operation.location(),
			"Operator " + std::string(TokenTraits::toString(_operation.getOperator())) + " not compatible with types "
				+ left->type->toString() + " and " + right->type->toString());
		return;
	}

	// Step 4: Convert operands to the result type
	left = convertType(left, *resultType);	 // Convert the left operand to the result type
	right = convertType(right, *resultType); // Convert the right operand to the result type

	// If either conversion fails, stop further processing
	if (!left || !right)
		return;

	// Step 5: Perform the binary operation
	if (std::optional<rational> value
		= evaluateBinaryOperator(_operation.getOperator(), left->value, right->value)) // Perform the operation
	{
		// Step 6: Convert the result to TypedRational
		std::optional<TypedRational> convertedValue
			= convertType(*value, *resultType); // Convert result to TypedRational
		if (!convertedValue)
			// If conversion fails, report a fatal error (likely an arithmetic issue)
			m_errorReporter
				.fatalTypeError(2643_error, _operation.location(), "Arithmetic error when computing constant value.");
		// Step 7: Cache the result
		m_values[&_operation] = convertedValue; // Cache the evaluated result
	}
}


/**
 * @brief Evaluates a literal value during constant expression evaluation.
 *
 * This function, a part of the Visitor pattern, is called when encountering a
 * Literal node in the AST. It attempts to determine the type of the literal
 * and convert it to a TypedRational representation if possible.  If a type
 * cannot be determined or the conversion fails, no value is stored in the cache.
 *
 * @param _literal The Literal AST node being visited.
 */
void ConstantEvaluator::endVisit(Literal const& _literal)

/*
Explanation and Example:
The endVisit(Literal const& _literal) function is responsible for handling literal values encountered in the AST during
constant expression evaluation. Its primary goal is to determine the type of the literal and, if possible, create a
TypedRational representation of it. Line-by-Line Breakdown:
	1. if (Type const* literalType = TypeProvider::forLiteral(_literal)):
		○ This line attempts to determine the type of the literal using a TypeProvider. The
TypeProvider::forLiteral(_literal) function likely examines the _literal object (representing the literal in the AST)
and determines its appropriate type based on its value and/or context. ○ If a type can be successfully determined, it is
stored in the literalType pointer. If a type cannot be determined, literalType will be nullptr.
	2. m_values[&_literal] = constantToTypedValue(*literalType);:
		○ If literalType is not nullptr (meaning a type was found), this line attempts to convert the literal to a
TypedRational using the constantToTypedValue function. ○ The result of constantToTypedValue is stored in the m_values
cache using the address of the _literal node as the key. ○ If constantToTypedValue returns std::nullopt (conversion
failed), nothing is added to the cache for this literal. Example: Suppose you have the following code snippet: const int
x = 123; // Here, 123 is a literal
*/
{
	// Attempt to get the type of the literal from the TypeProvider
	if (Type const* literalType = TypeProvider::forLiteral(_literal))
		// If a type is found, convert the literal to a TypedRational and store it
		m_values[&_literal] = constantToTypedValue(*literalType);
}

/**
 * @brief This function is called when the visitor encounters the end of an Identifier node
 *        during AST traversal. It attempts to evaluate constant variables.
 *
 * @param _identifier A constant reference to the Identifier AST node being visited.
 */
void ConstantEvaluator::endVisit(Identifier const& _identifier)
{
	// Attempt to dynamically cast the referenced declaration of the identifier's annotation
	// to a constant variable declaration.
	VariableDeclaration const* variableDeclaration
		= dynamic_cast<VariableDeclaration const*>(_identifier.annotation().referencedDeclaration);

	// If the cast is successful and the variable declaration represents a constant variable...
	if (variableDeclaration && variableDeclaration->isConstant())
	{
		// ...evaluate the variable declaration and store the resulting value in the `m_values` map,
		// using the address of the identifier as the key.
		m_values[&_identifier] = evaluate(*variableDeclaration);
	}
	// If the identifier does not refer to a constant variable, this function does nothing.
}

// Example usage:
//
// Suppose we have the following code:
//
//   const int x = 10;
//   int y = x + 5;
//
// When the `ConstantEvaluator` visitor reaches the end of the identifier `x` in the AST,
// `endVisit(Identifier const& _identifier)` is called:
//
// 1. `_identifier` represents the `x` identifier in the AST.
// 2. `_identifier.annotation().referencedDeclaration` retrieves the declaration of `x`.
// 3. `dynamic_cast<VariableDeclaration const*>` checks if the declaration is a `VariableDeclaration`
//    and if it is constant. In this case, it is both.
// 4. `variableDeclaration->isConstant()` returns true.
// 5. `evaluate(*variableDeclaration)` is called to evaluate the declaration of `x`,
//    which results in the value `10`.
// 6. `m_values[&_identifier] = 10` stores the value `10` in the `m_values` map,
//    associated with the address of the identifier `x`.
//
// This process allows the `ConstantEvaluator` to identify and store the values of
// constant variables encountered during AST traversal.

/**
 * @brief This function is called when the visitor encounters the end of an Identifier node
 *        during AST traversal. It attempts to evaluate constant variables.
 *
 * @param _identifier A constant reference to the Identifier AST node being visited.
 */
void ConstantEvaluator::endVisit(Identifier const& _identifier)
{
	// Attempt to dynamically cast the referenced declaration of the identifier's annotation
	// to a constant variable declaration.
	VariableDeclaration const* variableDeclaration
		= dynamic_cast<VariableDeclaration const*>(_identifier.annotation().referencedDeclaration);

	// If the cast is successful and the variable declaration represents a constant variable...
	if (variableDeclaration && variableDeclaration->isConstant())
	{
		// ...evaluate the variable declaration and store the resulting value in the `m_values` map,
		// using the address of the identifier as the key.
		m_values[&_identifier] = evaluate(*variableDeclaration);
	}
	// If the identifier does not refer to a constant variable, this function does nothing.
}

// Example usage:
//
// Suppose we have the following code:
//
//   const int x = 10;
//   int y = x + 5;
//
// When the `ConstantEvaluator` visitor reaches the end of the identifier `x` in the AST,
// `endVisit(Identifier const& _identifier)` is called:
//
// 1. `_identifier` represents the `x` identifier in the AST.
// 2. `_identifier.annotation().referencedDeclaration` retrieves the declaration of `x`.
// 3. `dynamic_cast<VariableDeclaration const*>` checks if the declaration is a `VariableDeclaration`
//    and if it is constant. In this case, it is both.
// 4. `variableDeclaration->isConstant()` returns true.
// 5. `evaluate(*variableDeclaration)` is called to evaluate the declaration of `x`,
//    which results in the value `10`.
// 6. `m_values[&_identifier] = 10` stores the value `10` in the `m_values` map,
//    associated with the address of the identifier `x`.
//
// This process allows the `ConstantEvaluator` to identify and store the values of
// constant variables encountered during AST traversal.
