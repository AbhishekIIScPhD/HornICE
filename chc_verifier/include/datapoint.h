/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef __CHCTEACHER_DATAPOINT_H__
#define __CHCTEACHER_DATAPOINT_H__

// C++ includes
#include <ostream>
#include <vector>
#include <algorithm>

// Z3 includes
#include "z3++.h"

// Project includes
#include "../../hice-dt/include/datapoint.h"

#define EXTRA

namespace chc_teacher
{
	
	class datapoint
	{

	public:

		z3::func_decl predicate;
		
		mutable std::vector<z3::expr> values;
		
		datapoint(const z3::func_decl & predicate, std::vector<z3::expr> && values)
			: predicate(predicate), values(std::move(values))
		{
			
			// Check that all data is in fact data
			for (const auto & v : values)
			{
				assert (v.is_const());
			}
		}

		unsigned hash () const {

			unsigned hashValue = predicate.hash();

			for (const auto & v : values) {
				hashValue += v.hash();
			}

			return hashValue;
		}

		bool equal (const chc_teacher::datapoint & dp2) const {

			if (!z3::eq(predicate, dp2.predicate)) {

				return false;

			} else {

				auto it_first = values.begin();
				auto it_second = dp2.values.begin();

				while (it_first != values.end() || it_second != dp2.values.end()) {

					if (!z3::eq(*it_first, *it_second)) {

						return false;
					}
					it_first++;
					it_second++;
				}
			}
			return true;
		}

		std::vector<unsigned int> get_categorical_data(std::unordered_map<z3::func_decl, unsigned, ASTHasher, ASTComparer> relation2ID) const{

			std::vector<unsigned int> _categorical_data;

			_categorical_data.push_back(relation2ID.find(predicate)->second);

#ifdef DEBUG
			std::cout << __FUNCTION__ << " Categorical Data Predicate : "<< " length :" << _categorical_data.end() - _categorical_data.begin() << predicate << " ID :" << relation2ID.find(predicate)->second << "\n";
#endif		
			// for (auto const cat: _categorical_data) {
			// 	std::cout << "Categorical data: " << cat << "\n";
			// }
			return _categorical_data;
		}

	  std::vector<int> get_int_data(std::unordered_map<z3::func_decl, unsigned, ASTHasher, ASTComparer> relation_to_base_value, unsigned number_of_int_attributes) const{

			//
			// Adding derived attributes
			//

			auto size_of_basic_attributes = values.size();
#ifdef DEBUG
			std::cout << "In::" << __FUNCTION__ << "\n";

			std::cout << __FUNCTION__ << ":: #Basic Attributes : " << size_of_basic_attributes << " Integer Attributes : " << number_of_int_attributes << "\n";
#endif

			std::cout << __FUNCTION__ <<"::Printing integer attributes\n";

			// for (auto const attr:int_names){
			//   std::cout << __FUNCTION__ <<"::Int Attr" << attr << "\n";
			// }
			
// 			if (size_of_basic_attributes == 4){
// #ifdef DEBUG
// 			  std::cout << __FUNCTION__ << "Added new values to the integer value vector" << size_of_basic_attributes << "\n";
// #endif
// 			  values.push_back(((values.at(3) + values.at(2)) - values.at(1)).simplify());
// 			  std::cout << __FUNCTION__ << "::Values at 3::" << values.at(3) << "\n";
// 			  std::cout << __FUNCTION__ << "::Values at 2::" << values.at(2) << "\n";
// 			  std::cout << __FUNCTION__ << "::Values at 1::" << values.at(1) << "\n";
// 			  std::cout << __FUNCTION__ << "::Values added ::" << (values.at(3) + values.at(2) - values.at(1)).simplify();
// 			}

#ifdef EXTRA
			if(size_of_basic_attributes > 2)
			  {
			    for (unsigned first_index = 0; first_index < size_of_basic_attributes; first_index++) {
			      for (unsigned second_index = first_index+1; second_index < size_of_basic_attributes; second_index++) {
				for (unsigned third_index = first_index+2; third_index < size_of_basic_attributes; third_index++) {
				  if (values.at(first_index).get_sort().is_int() && values.at(second_index).get_sort().is_int()&& values.at(third_index).get_sort().is_int()) {
				    std::vector<int> numbers;
				    numbers.push_back(first_index);
				    numbers.push_back(second_index);
				    numbers.push_back(third_index);
				    
				    std::sort(numbers.begin(), numbers.end());

				    // Generate all permutations
				    do {
				      //==================
				      values.push_back((values.at(numbers[0]) + values.at(numbers[1]) + values.at(numbers[2])).simplify());

				      //==================					      
				      values.push_back((values.at(numbers[0]) - values.at(numbers[1]) - values.at(numbers[2])).simplify());

				      //==================
				      values.push_back((values.at(numbers[0]) + values.at(numbers[1]) - values.at(numbers[2])).simplify());

				      //==================
				      values.push_back((values.at(numbers[0]) - values.at(numbers[1]) + values.at(numbers[2])).simplify());

				    } while (std::next_permutation(numbers.begin(), numbers.end()));
				  }
				}
			      }
			    }
			  }
#endif
			
			for (unsigned first_index = 0; first_index < size_of_basic_attributes; first_index++) {

				for (unsigned second_index = first_index + 1; second_index < size_of_basic_attributes; second_index++) {

					if (values.at(first_index).get_sort().is_int() && values.at(second_index).get_sort().is_int()) {

						values.push_back((values.at(first_index) + values.at(second_index)).simplify());

						values.push_back((values.at(first_index) - values.at(second_index)).simplify());
					}
				}
			}

			std::vector<int> _int_data;

			for (unsigned int_data_index = 0; int_data_index <= number_of_int_attributes; int_data_index++) {

				if ((int_data_index < relation_to_base_value.find(predicate)->second)||(int_data_index >= (relation_to_base_value.find(predicate)->second + values.size()))) {
					_int_data.push_back(0);
				} else {
					for (const auto & expr : values) {
						assert (expr.is_const());
						int value;
						if (expr.is_bool()) {
							value = expr.bool_value(); // Bool value (should be casted to int as well), implicit conversion happens here
						} else if (expr.is_int()) {
							auto conversion_result = Z3_get_numeral_int(expr.ctx(), expr, &value); // Integer value
							assert (conversion_result);
						} else {
							throw std::runtime_error("Unsupported value type"); // Unsupported type of value
						}
						_int_data.push_back(value);
						int_data_index++;
					}
				}
			}
			return _int_data;
		}

		
		friend std::ostream & operator<<(std::ostream & out, const datapoint & dp)
		{
		
			out << dp.predicate.name() << "(";

			int basic_attrs = dp.predicate.arity();
			for (unsigned i = 0; i < basic_attrs; ++i)
			{
				out << (i > 0 ? ", " : "") << dp.values[i];
			}
			
			out << ")";
		
			return out;
		
		}
		
	};

}; // End namespace chc_teacher

#endif
