#include "pugixml.hpp"

#include <algorithm>
#include <iostream>
#include <random>
#include <string>

void negate_content (pugi::xml_node &orig) {
  pugi::xml_node negation {orig.parent ().append_child ("Unary_Pred")};
  negation.append_attribute ("op") = "not";
  negation.append_move (orig);
}

inline std::string lemmatize_out_file (std::string out_file) {
  size_t ext {out_file.rfind ('.')};
  return out_file.substr (0, ext);
}

void negate_goal (pugi::xml_document &doc, std::string negate_file) {
  for (pugi::xml_node &child : doc.first_child ().children ("Proof_Obligation")) {
    for (pugi::xml_node &simple_goal : child.children ("Simple_Goal")) {
      pugi::xml_node content {simple_goal.child ("Goal").first_child ()};
      negate_content (content);
    }
  }

  negate_file += "_negated_goals.pog";

  doc.save_file (negate_file.c_str ());
}

void negate_hypotheses (pugi::xml_document &doc, std::string negate_file,
			int regen_count, double neg_rate, std::mt19937 &rng) {
  for (int i {0}; i < regen_count; ++i) {
    bool unchanged {true};
    pugi::xml_document version;
    version.reset (doc);

    auto maybe_negate
      { [&rng, neg_rate] (pugi::xml_node &&child) {
	std::uniform_real_distribution<> urd {0.0, 1.0};
	if (urd (rng) < neg_rate) {
	  negate_content (child);
	  return true;
	}
	return false;
      }};

    for (pugi::xml_node &child : version.first_child ().children ("Proof_Obligation")) {
      for (pugi::xml_node &hyp : child.children ("Hypothesis"))
	{ unchanged = maybe_negate (hyp.first_child ()) ? false : unchanged; }
      for (pugi::xml_node &hyp : child.children ("Local_Hyp"))
	{ unchanged = maybe_negate (hyp.first_child ()) ? false : unchanged; }
    }

    if (unchanged)
      { continue; }
    std::string output {negate_file + "_h_" + std::to_string (neg_rate)
			+ '_' + std::to_string (i) + ".pog"};
    version.save_file (output.c_str ());
  }
}

void remove_goal (pugi::xml_document &doc, std::string removed_file) {
  for (pugi::xml_node &child : doc.first_child ().children ("Proof_Obligation")) {
    for (pugi::xml_node &simple_goal : child.children ("Simple_Goal"))
      { simple_goal.remove_child ("Goal"); }
  }

  removed_file += "_removed_goals.pog";

  doc.save_file (removed_file.c_str ());
}
      
int main (int argc, char **argv) {
  std::string help {"Usage: ./bench_sat -i <in_file> -o <out_file> [-h -n <hypothesis_negation_rate> -c <number_of_new_versions>]"};
  if (argc < 5) {
    std::cerr << help << '\n';
    return 1;
  }
  
  int in_file_arg {};
  std::string out_file;

  double neg_rate {};
  int regen_count {};
  bool neg_goal {true};
  
  for (int i {1}; i < argc; ++i) {
    switch (argv[i][1]) {
    case 'i':
      in_file_arg = ++i;
      break;
    case 'o':
      out_file = argv[++i];
      break;
    case 'h':
      if (argc != 10) {
	std::cerr << "-h must be accompanied by:\n"
		  << "the probability that a hypothesis be negated after its option flag, -n, and\n"
		  << "the number of versions to generate after its option flag, -c.\n\n"
		  << help << '\n';
	return 1;
      }
      neg_goal = false;
      break;
    case 'n':
      neg_rate = std::stod (argv[++i]);
      break;
    case 'c':
      regen_count = std::stoi (argv[++i]);
      break;
    default:
      std::cerr << argv[i] << " unrecognized.\n\n"
		<< help << '\n';
      return 1;
    }
  }

  std::string out_file_root {lemmatize_out_file (out_file)};

  pugi::xml_document doc;
  doc.load_file (argv[in_file_arg]);

  if (neg_goal)
    { negate_goal (doc, out_file_root); }
  else {
    if (neg_rate <= 0 || neg_rate > 1) {
      std::cerr << "Hypothesis negation rate must be within (0, 1].\n\n"
		<< help << '\n';
      return 1;
    }
    else if (regen_count <= 0) {
      std::cerr << "Must generate at least one new file.\n\n"
		<< help << '\n';
      return 1;
    }
    else {
      std::random_device rd;
      std::mt19937 rng {rd ()};
      negate_hypotheses (doc, out_file_root, regen_count, neg_rate, rng);
    }
  }

  return 0;
}
