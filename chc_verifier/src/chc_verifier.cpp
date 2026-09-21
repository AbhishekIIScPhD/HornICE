/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// C++ includes
#include <functional>
#include <iostream>
#include <list>
#include <chrono>
#include <ctime>
#include <getopt.h>
#include <unistd.h>

#include <fstream>
#include <sstream>
#include <string>
#include <vector>

// Z3 includes
#include "z3++.h"

// Project includes
#include "seahorn_smtlib2_parser.h"
#include "chc_verifier.h"
#include "conjecture.h"
#include "learner_interface.h"
#include "derived_pred.h"



// #define DEBUG
//#define OTHER_1
#define CONJ
#define CTX
// #define CONJ_1

// #define COND if(learner_invocations == 57)

#define COND if(false)

#define INFUN std::cout<<"In "<<__FUNCTION__<<"\n"

using namespace chc_teacher;


std::list<std::unique_ptr<horn_counterexample>> g_all_counterexamples;
 // Forward declaration for the helper functions
 datapoint parse_datapoint(z3::context & ctx, const problem & p, std::string s);
 std::list<datapoint> parse_datapoint_list(z3::context & ctx, const problem & p, std::string s);

 /**
  * @brief Parses a string representation of a single datapoint.
  * e.g., "inv1(0, 1, 0, 0)"
  */
 datapoint parse_datapoint(z3::context & ctx, const problem & p, std::string s) {
  //   s.erase(std::remove_if(s.begin(), s.end(), isspace), s.end());
 	   // Trim leading/trailing whitespace from the whole string first
 	   s.erase(0, s.find_first_not_of(" \t\n\r"));
 	   s.erase(s.find_last_not_of(" \t\n\r") + 1);

     auto open_paren = s.find('(');
     //auto close_paren = s.find(')');
 	   auto close_paren = s.rfind(')');

     if (open_paren == std::string::npos || close_paren == std::string::npos) {
         throw std::runtime_error("Invalid datapoint format: " + s);
     }

     std::string pred_name = s.substr(0, open_paren);
     std::string args_str = s.substr(open_paren + 1, close_paren - open_paren - 1);

     // Find the corresponding func_decl from the problem's relations
     z3::func_decl predicate(ctx);
     bool found = false;
     for (const auto& rel : p.relations) {
         if (rel.name().str() == pred_name) {
             predicate = rel;
             found = true;
             break;
         }
     }

     if (!found) {
         throw std::runtime_error("Unknown predicate name: " +  pred_name);
     }

     // Parse arguments
     std::vector<z3::expr> values;
     std::stringstream ss(args_str);
     std::string arg;
     while (std::getline(ss, arg, ',')) {
         if (arg.empty()) continue;
         try {
            	// Trim whitespace from the individual argument
            	arg.erase(0, arg.find_first_not_of(" \t\n\r"));
            	arg.erase(arg.find_last_not_of(" \t\n\r") + 1);

            	if (arg == "true") {
            		values.push_back(ctx.bool_val(true));
            	} else if (arg == "false") {
            		values.push_back(ctx.bool_val(false));
            	} else {
            		// Handle potential parens around negative numbers
            		if (arg.front() == '(' && arg.back() == ')') {
            			arg = arg.substr(1, arg.length() - 2);
            			arg.erase(std::find(arg.begin(), arg.end(), ' '));
            		}
            		values.push_back(ctx.int_val(std::stoi(arg)));
            	}
           //values.push_back(ctx.int_val(std::stoi(arg)));
           } catch (const std::invalid_argument& ia) {
            throw std::runtime_error("Invalid integer argument: " + arg);
            throw std::runtime_error("Invalid argument format: " + arg);
           }
             //values.push_back(ctx.int_val(std::stoi(arg)));
         // } catch (const std::invalid_argument& ia) {
         //     throw std::runtime_error("Invalid integer argument: " +  arg);
         // }
     }

     return datapoint(predicate, std::move(values));
 }

 /**
  * @brief Parses a string representation of a list of datapoints.
  * e.g., "{inv1(0, 1, 0, 0), pu(0, 1)}"
  */
 std::list<datapoint> parse_datapoint_list(z3::context & ctx, const problem & p, std::string s) {
     std::list<datapoint> dps;
     //s.erase(std::remove(s.begin(), s.end(), ' '), s.end());

 	// Trim whitespace from the whole string
 	    s.erase(0, s.find_first_not_of(" \t\n\r"));
 	    s.erase(s.find_last_not_of(" \t\n\r") + 1);

 	    // if (s.length() <= 2) return dps; // Empty list "{}"
 	    if (s.length() <= 2 || s == "{}") return dps; // Empty list

     if (s.length() <= 2) return dps;

     s = s.substr(1, s.length() - 2);

     size_t start = 0;
     int paren_count = 0;
     for (size_t i = 0; i < s.length(); ++i) {
         if (s[i] == '(') {
             paren_count++;
         } else if (s[i] == ')') {
             paren_count--;
             if (paren_count == 0) {
             	     // When a full "predicate(...)" is found, parse it
							    if (i + 1 == s.length() || s[i+1] == ',') {
							         dps.push_back(parse_datapoint(ctx, p, s.substr(start, i - start + 1)));
							         start = i + 2; // Move past the ')' and the potential ','
							    }
                 // dps.push_back(parse_datapoint(ctx, p, s.substr(start, i - start + 1)));
                 // start = i + 2;
             }
         }
     }
     return dps;
 }

 /**
  * @brief Parses a string representation of a counterexample back into an object.
  */
 std::unique_ptr<horn_counterexample> parse_counterexample_from_string(z3::context & ctx, const problem & p, const std::string & line) {
     auto separator = line.find("=>");
     if (separator == std::string::npos) {
         std::cerr << "Error: Invalid counterexample format (missing =>): " << line << std::endl;
         return nullptr;
     }

     try {
         std::string lhs_str = line.substr(0, separator);
         std::string rhs_str = line.substr(separator + 2);

         auto lhs = parse_datapoint_list(ctx, p, lhs_str);
         auto rhs = parse_datapoint_list(ctx, p, rhs_str);

         return std::make_unique<horn_counterexample>(std::move(lhs), std::move(rhs));
     } catch (const std::exception& e) {
         std::cerr << "Error parsing counterexample: " << e.what() << " in line: " << line << std::endl;
         return nullptr;
     }
 }

 /**
  * @brief Loads a list of counterexamples from a given file.
  */
 std::list<std::unique_ptr<horn_counterexample>> load_counterexamples(z3::context & ctx, const problem & p, const std::string & filename) {
     std::list<std::unique_ptr<horn_counterexample>> loaded_counterexamples;
     std::ifstream infile(filename);
     if (!infile) {
         std::cerr << "Warning: Could not open counterexample input file: " << filename << std::endl;
         return loaded_counterexamples;
     }

     std::string line;
     const std::string prefix = "Counterexample: ";
     while (std::getline(infile, line)) {
         if (line.rfind(prefix, 0) == 0) {
             std::string content = line.substr(prefix.length());
             auto ce = parse_counterexample_from_string(ctx, p, content);
             if (ce) {
                 loaded_counterexamples.push_back(std::move(ce));
             }
         }
     }
     std::cout << "Loaded " << loaded_counterexamples.size() << " counterexamples from " << filename << std::endl;
     return loaded_counterexamples;
 }

 /**
  * @brief Dumps a list of counterexamples to a given file.
  */
 void dump_counterexamples(const std::list<std::unique_ptr<horn_counterexample>>& counterexamples, const std::string& filename) {
     std::ofstream outfile(filename, std::ios::trunc | std::ios::out);
     if (!outfile) {
         std::cerr << "Error: Could not open counterexample output file: " << filename << std::endl;
         return;
     }

     for (const auto &counter : counterexamples) {
         if (counter) {
             outfile << "Counterexample: " << *counter << "\n";
         }
     }
     std::cout << "Dumped " << counterexamples.size() << " counterexamples to " << filename << std::endl;
 }

void learn1(z3::context & ctx, const problem & p, bool do_horndini_prephase, bool use_bounds)
{
	learner_interface learner(p.relations, do_horndini_prephase, use_bounds);
	std::unordered_map<z3::func_decl, conjecture, ASTHasher, ASTComparer> previous_conjectures;
	bool finished = false;
	unsigned checked_chcs = 0;
	unsigned learner_invocations = 0;
	
	while (!finished)
	{		
		finished = true;
		
		// Get conjectures
		auto conjectures = learner.get_conjectures();
		++learner_invocations;
		
		
		//
		// Check each CHC and return counterexample if detected
		//
		for (const auto & chc : p.chcs)
		{
			
			// Check CHC
			auto counterexample = chc_verifier::check_chc(ctx, chc, conjectures);
			++checked_chcs;
			
			// If no counterexample was found, report success
			if (counterexample != nullptr)
			{
			
				learner.add_counterexample(*counterexample);
				finished = false;
				break;
			}

		}
		
		previous_conjectures = std::move(conjectures); // No use of conjectures beyond this point!		
		
	}

	
	assert (chc_verifier::naive_check(ctx, p, previous_conjectures) == nullptr);


	//
	// Output solution
	//
	// std::cout << "Success (checked " << checked_chcs << " CHCs, invoked learner " << learner_invocations << " times)" << std::endl;
	//for (const auto & c : previous_conjectures)
	{
		// std::cout << c.first << " => " << c.second << std::endl;				
	}
	
}


std::unordered_map<z3::func_decl, conjecture, ASTHasher, ASTComparer>
//learn2(z3::context & ctx, problem & p, bool do_horndini_prephase, bool use_bounds, std::list<std::unique_ptr<horn_counterexample>> && seeded_counterexamples)
learn2(z3::context & ctx, const problem & p, bool do_horndini_prephase, bool use_bounds)
{
  INFUN;
	// Prepare auxiliary variables and data structures
	learner_interface learner(p.relations, do_horndini_prephase, use_bounds);
	std::list<std::reference_wrapper<const constrainted_horn_clause>> satisfied_chcs;
	std::list<std::reference_wrapper<const constrainted_horn_clause>> unsatisfied_chcs;
	std::unordered_map<z3::func_decl, conjecture, ASTHasher, ASTComparer> previous_conjectures;
	unsigned checked_chcs = 0;
	unsigned learner_invocations = 0;
	// std::list<std::unique_ptr<horn_counterexample>> all_counterexamples;

 	std::list<std::unique_ptr<horn_counterexample>> all_counterexamples = std::move(g_all_counterexamples);

	// Seed the learner with pre-loaded counterexamples
	for (const auto& ce : all_counterexamples) {
	   if (ce) {
	       learner.add_counterexample(*ce);
	   }
	}
	
	// All CHCs are unchecked
	for (const auto & chc : p.chcs)
	{
		unsatisfied_chcs.push_back(chc);
	}

	//
	// Run learning loop
	//
	while (!unsatisfied_chcs.empty())
	{
		std::cout << "===========================================\n";
		std::cout << "Learning Iteration: " << learner_invocations << "\n";
		std::cout << "===========================================\n";
		
		// Get conjectures
		auto conjectures = learner.get_conjectures();


		++learner_invocations;

#ifdef CONJ
		COND{
		  std::cout << "\n=========================\n";
		  std::cout << "Printing the conjectures" << "\n";

		  for (const auto& conjecture : conjectures) {
		    // std::cout << "Conjecture: " << "F : " << conjecture.first <<  "S : " << conjecture.second << "\n";
		    std::cout << "Conjecture: " << conjecture.first << conjecture.second << "\n";
		  }
		  std::cout << "=========================\n";
		}
#endif

#ifdef CONJ_1
		COND{
		std::cout << "\n=========================\n";
		std::cout << "Printing the previous conjectures" << "\n";

		for(auto const &prev_conj : previous_conjectures) {
			std::cout << "Prev Conjecture: " << prev_conj.first << prev_conj.second << "\n";
		}
		std::cout << "=========================\n";
		}
#endif

#ifdef DEBUG
		COND{
		std::cout << "\n\n=========================";
		std::cout << "\nPrinting Satisfied CHCs" << "\n";

		for(auto const &sat_chc : satisfied_chcs) {
			std::cout << "Satisfied CHC: " << sat_chc << "\n";
		}
		std::cout << "\n=========================\n";
		}
#endif

#ifdef DEBUG
		COND{
		std::cout << "=========================\n";
		std::cout << "Printing Unsatisfied CHCs" << "\n";

		for(auto const &unsat_chc : unsatisfied_chcs) {
			std::cout << "Unsatisfied CHC: " << unsat_chc << "\n";
		}
		std::cout << "=========================\n";
		}
#endif
		
		// Check which conjectures have changed
		std::unordered_map<z3::func_decl, bool, ASTHasher, ASTComparer> changed(conjectures.size());
		bool all_as_before = true;
		for (const auto & pair : conjectures)
		{
			
			// Get old conjecture for declaration (if exists)
			auto previous_conjecture_it = previous_conjectures.find(pair.first);
			
			// Store whether conjecture has changed
			auto has_changed = (previous_conjecture_it == previous_conjectures.end() || !(pair.second == previous_conjecture_it->second));
			changed[pair.first] = has_changed;
			if (has_changed)
			{
				all_as_before = false;
			}

		}

		//assert (!all_as_before);

		// DEBUG
		// std::cout << "---------- Changes of conjectures ----------" << std::endl;
		//for (const auto & status : changed)
		{
			// std::cout << status.first << ": " << status.second << std::endl;
		}
		// std::cout << "Unsatisfied CHCs: " << unsatisfied_chcs.size() << "; satisfied CHCs: " << satisfied_chcs.size() << std::endl;
		
		
		
		// Data structure to maintain counterexamples
		std::list<std::unique_ptr<horn_counterexample>> counterexamples;
		std::list<std::reference_wrapper<const constrainted_horn_clause>> now_satisfied_chcs;

		
		// Check previously unsatisfied chcs
		// std::cout << "++++++++++ UNSATISFIED CHCS ++++++++++" << std::endl;
		auto unsat_it = unsatisfied_chcs.begin();
		while (unsat_it != unsatisfied_chcs.end())
		{
			
			// Check whether a conjecture has changed
			bool has_changed = false;
			for (const auto & decl : unsat_it->get().uninterpreted_predicates)
			{
				if (changed.at(decl))
				{
					has_changed = true;
					break;
				}
			}
			
			
			// Check if some conjecture changed
			if (has_changed)
			{

				auto counterexample = chc_verifier::check_chc(ctx, *unsat_it, conjectures);
				++checked_chcs;
				
				// CHC is not satisfied, counterexample is returned
				if (counterexample != nullptr)
				{
#ifdef OTHER
				  COND{
					std::cout << "Unsatisfied (Previosuly Unsatisfied CHC): " << *unsat_it << "with counterexample :" << *counterexample <<"\n";
				  }
#endif
				  all_counterexamples.push_back(std::make_unique<horn_counterexample>(*counterexample));
				  counterexamples.push_back(std::move(counterexample)); // NO use of variable counterexample beyond this point
					
#ifdef OTHER_1
				  COND{
				    std::cout << "Unsat CHC Printing All Counterexamples" << "#" << counterexamples.size() << "\n";
				    for ( auto &cexam : counterexamples) {
				      std::cout << "Horn Counterexmple :" << *cexam << "\n";
				    }
				  }
#endif

					++unsat_it;
				}
				// CHC is now satisfied
				else
				{
					now_satisfied_chcs.push_back(*unsat_it);
#ifdef OTHER_1
					COND{
					std::cout << "Satisfied (Previously Unsatisfied CHC): " << *unsat_it << "\n";
					}
#endif
					unsat_it = unsatisfied_chcs.erase(unsat_it);
				}

			}
			else
			{
				++unsat_it;
				std::cout << "Unsat Formula";
			}
		}

		// Check previously satisfied CHC if it contains a conjecture that has changed in the last round
		// std::cout << "++++++++++ SATISFIED CHCS ++++++++++" << std::endl;
		auto sat_it = satisfied_chcs.begin();
		while (sat_it != satisfied_chcs.end())
		{
			
			// Check whether a conjecture has changed
			bool has_changed = false;
			for (const auto & decl : sat_it->get().uninterpreted_predicates)
			{
				if (changed.at(decl))
				{
					has_changed = true;
					break;
				}
			}
			
			// Check if some conjecture changed
			if (has_changed)
			{
				
				auto counterexample = chc_verifier::check_chc(ctx, *sat_it, conjectures);
				++checked_chcs;
				
				// CHC is not satisfied, counterexample is returned
				if (counterexample != nullptr)
				{
#ifdef OTHER
				  COND{
					std::cout << "Unsatisfied (Previously Satisfied CHC): " << *sat_it << "with counterexample :" << *counterexample << "\n";
				  }
#endif
				  all_counterexamples.push_back(std::make_unique<horn_counterexample>(*counterexample));
					counterexamples.push_back(std::move(counterexample)); // NO use of variable counterexample beyond this point
#ifdef OTHER_1
					COND{
					std::cout << "SatCHC Printing All Counterexample"  << "#" << counterexamples.size() << "\n";
					for ( auto &cexam : counterexamples) {
						std::cout << "Horn Counterexmple :" << *cexam << "\n";
					}
					}
#endif
					unsatisfied_chcs.push_back(*sat_it);
					sat_it = satisfied_chcs.erase(sat_it);
				}
				// CHC is now satisfied
				else
				{
#ifdef OTHER_1
				  COND{
					std::cout << "Satisfied (Previously Satisfied CHC): " << sat_it->get().expr << "\n";
				  }
#endif
					++sat_it;
				}
				
			}
			else
			{
				++sat_it;
			}
			
		}		
		
		
		// Add now satisfied CHCs
		satisfied_chcs.insert(satisfied_chcs.end(), std::make_move_iterator(now_satisfied_chcs.begin()), std::make_move_iterator(now_satisfied_chcs.end()));


#ifdef CTX
		//if(unsatisfied_chcs.empty()){
		  std::cout << "Printing all the counter examples : " << all_counterexamples.size() << "\n";
		  for (const auto &counter: all_counterexamples) {
		    std::cout << "Counterexample: " << *counter << "\n";
		  }		  
		//}
#endif
std::cout << "Conjectures\n";
		for (const auto & c : previous_conjectures)
		{
			std::cout << c.first << " => " << c.second << std::endl;
		}

		
		// Add counterexamples 		
		for (const auto & ce : counterexamples)
		{
			learner.add_counterexample(*ce);
		}
		
		previous_conjectures = std::move(conjectures); // No use of conjectures beyond this point!
	}


	
	assert (chc_verifier::naive_check(ctx, p, previous_conjectures) == nullptr);

  // Move the final list of counterexamples back into the global variable
 	g_all_counterexamples = std::move(all_counterexamples);


	//
	// Output solution
	//
	std::cout << "Success (checked " << checked_chcs << " CHCs, invoked learner " << learner_invocations << " times)" << std::endl;
	for (const auto & c : previous_conjectures)
	{
	  std::cout << c.first << " => " << c.second << std::endl;
	  //std::cout << "Simplified Formual\n";
#ifdef OTHER_1
	  std::cout << c.first << " => " << c.second.expr.simplify() << std::endl;
#endif
	}


    std::cout << "Final Relations read" << "\n";
	for (auto relation : p.relations) {
		std::cout << "Relation : " << relation.arity() << relation << relation.name() << "\n";
	}

	std::cout << "Final CHCs read" << "\n";
	for (auto ch : p.chcs) {
		for(auto pred : ch.predicates_in_lhs) {
			std::cout << "CHC : " << pred << "\n";
		}
	}
	return previous_conjectures;
}



/**
 * Prints a help message to an output stream.
 *
 * @param out The output stream to write to
 * @param name The name of the program
 */
void print_help(std::ostream & out, const char * name)
{
	out << "Usage: " << name << " [options] file" << std::endl;
	out << "Options are:" << std::endl;
	out << "  -b\t\tBound the learner" << std::endl;
	out << "  -h\t\tRun Horndini pre-phase" << std::endl;
 	out << "  -f <file>\t file for counterexamples" << std::endl;
}


std::vector<predTemp> extractAttributes(std::ifstream &relAttrs) {

	std::vector<predTemp> preds;
	std::string line;

	while (std::getline(relAttrs, line)) {
		if (line.empty()) continue;

		std::istringstream header(line);
		chc_teacher::predTemp p;
		header >> p.relName >> p.numAttrs >> p.numDerAttr;

		for (int i = 0; i < p.numAttrs && std::getline(relAttrs, line); ++i) {
			std::istringstream attrLine(line);
			int id;
			std::string name;
			attrLine >> id >> name;
			p.argID[name] = id;
		}

		// Read derived attributes until next header or EOF
		for (int i = 0; i < p.numDerAttr && std::getline(relAttrs, line); ++i) {
			if (line.empty()) continue;
			p.derAttr.push_back(line);
		}

		preds.push_back(std::move(p));
	}

	return preds;
}


int main(int argc, char * argv[])
{


	/// Store the starting time of execution.
	 std::clock_t c_start = std::clock();


	//
	// Process command line arguments
	//
	bool do_horndini_prephase = false;
	bool use_bounds = true;
 	std::string cex_file;

	int c;
	//while ((c = getopt (argc, argv, "bh")) != -1)
 	while ((c = getopt (argc, argv, "bhf:")) != -1)
	{

		switch (c)
		{
			case 'b':
				use_bounds = true;
				break;
				
			case 'h':
				do_horndini_prephase = true;
				break;

			case 'f':
			  cex_file = optarg;
			  break;

			default:
				print_help(std::cout, argv[0]);
				return EXIT_FAILURE;
		}
	}

	if (optind+3 != argc)
	{
		std::cout << "Invalid input file specified" << std::endl;
		print_help(std::cout, argv[0]);
		return EXIT_FAILURE;
	}


	// File stem
	auto filename = std::string(argv[optind]);
	auto specGenFile = std::string(argv[++optind]);
	auto relAttrFile = std::string(argv[++optind]);
	std::ofstream specFile(specGenFile, std::ios::trunc|std::ios::out);

	std::ifstream relAttrs(relAttrFile); // contains custom templates for each relation
	if (!relAttrs) throw std::runtime_error("Failed to open file: " + filename);


	//
	// Create Z3 context and parse
	//
	z3::context ctx;
	auto p = seahorn_smtlib2_parser::parse(ctx, filename);
	std::cout << __FUNCTION__ << "::parsed \n"<< p << std::endl;

	std::cout << "Printing parse CHCs and relations\n";
	for(auto chc : p.chcs) {
		std::cout << "chc :: " << chc << "\n";
	}

	for(auto rel : p.relations) {
		std::cout << "rel :: " << rel << "\n";
	}

 	// Load counterexamples from file if specified
  //std::list<std::unique_ptr<horn_counterexample>> seeded_counterexamples;
  if (!cex_file.empty()) {
      g_all_counterexamples = load_counterexamples(ctx, p, cex_file);
  }
	//
	// Learn
	//
	//learn1(ctx, p); // Simple (original)
	std::vector<chc_teacher::predTemp> derPreds = extractAttributes(relAttrs);

	chc_teacher::derived_predicates = derPreds;
	auto conjectures = learn2(ctx, p, do_horndini_prephase, use_bounds); // Improved?

 	//auto conjectures = learn2(ctx, p, do_horndini_prephase, use_bounds, std::move(g_all_counterexamples)); // Improved?
   // Dump all counterexamples to file if specified
   if (!cex_file.empty()) {
       dump_counterexamples(g_all_counterexamples, cex_file);
  }
	specFile << conjectures.size() << "\n";
	for (auto conjecture : conjectures) {
		specFile << conjecture.first.name() << "\n";
		specFile <<  conjecture.first << "\n";
		specFile << "==>" << conjecture.second << "\n";
	}
	/*for (const auto & c : p){
		std::cout << c.first << " => " << c.second << std::endl;
	}*/

	/// Store the finishing time of execution.
	std::clock_t c_end = std::clock();

	std::cout << "Total time: " << ((c_end-c_start)*100 / CLOCKS_PER_SEC)/100.00 << std::endl;

}
