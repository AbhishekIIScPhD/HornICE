/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef __CHCTEACHER_CONJECTURE_H__
#define __CHCTEACHER_CONJECTURE_H__

// C++ includes
#include <ostream>

// Z3 includes
#include "z3++.h"


namespace chc_teacher
{

	class conjecture
	{

	public:

		z3::expr expr;
		
		z3::expr_vector variables;

		conjecture(const z3::expr & expr, const z3::expr_vector & variables)
			: expr(expr), variables(variables)
		{
			// Nothing
		}
		

		bool operator==(const conjecture & other) const
		{
			
			if (&other == this)
			{
				return true;
			}
			
			// Compare variables
			if (variables.size() != other.variables.size())
			{
				return false;
			}
			else
			{
				for (unsigned i = 0; i < variables.size(); ++i)
				{
					if (!z3::eq(variables[i], other.variables[i]))
					{
						return false;
					}
				}
			}
			
			
			// Compare expression
			return z3::eq(expr, other.expr);
			
		}
		
		friend std::ostream & operator<<(std::ostream & out, const conjecture & c)
		{
			
			out << "[";
			for (unsigned i = 0; i < c.variables.size(); ++i)
			{
				out << (i == 0 ? "" : ", ") << c.variables[i];
			}
			out << "] -> " << removeFormatting(c.expr);
			
			return out;
			
		}

		static std::string removeFormatting(const z3::expr& expr) {
			std::string str = Z3_ast_to_string(expr.ctx(), expr);
			std::string result;
			result.reserve(str.length());

			// Flag to track if we just added a space
			bool lastWasSpace = true;

			for (const char c : str) {
				if (std::isspace(c)) {
					if (!lastWasSpace) {
						result += ' ';
						lastWasSpace = true;
					}
				} else {
					result += c;
					lastWasSpace = false;
				}
			}
			// Remove trailing space if exists
			if (!result.empty() && result.back() == ' ') {
				result.pop_back();
			}
			return result;
		}
	};
}; // End namespace chc_teacher

#endif
