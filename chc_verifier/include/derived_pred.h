#include <string>
#include <map>
#include <vector>

#ifndef __CHCTEACHER_DER_ATTR_H__
#define __CHCTEACHER_DER_ATTR_H__
namespace chc_teacher{

	struct predTemp {
		std::string relName;
		int numAttrs; // attributes of a relation
		std::map<std::string, int> argID; // mapping id to the relation attribute
		int numDerAttr; // number of derived attributes
		std::vector<std::string> derAttr; // derived attributes
	};

	std::vector<predTemp> derived_predicates;
};

#endif