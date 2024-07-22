#include <chrono>
#include <ctime>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>

struct Constant {
  std::set<int> elements;
  #ifdef THRESHOLD
  double threshold {(THRESHOLD)};
  #else
  double threshold {0.6};
  #endif
  int own_number;
  int set_count;
  
  Constant (std::mt19937 &mt, int set_count, int own_number)
    : own_number {own_number}, set_count {set_count} {
    while (add (mt, set_count));
  }

  bool add (std::mt19937 &mt, int set_count) {
    std::uniform_real_distribution<> distr {0.0, 1.0};
    if (distr (mt) > threshold) {
      elements.insert ((int) (distr (mt) * set_count + 0.5));
      return true;
    }
    return false;
  }
};

std::ostream &operator << (std::ostream &out, Constant &con) {
  out << 'c' << con.own_number << " <: NAT";
  if (con.elements.size () > 0) {
    for (int el {0}; el <= con.set_count; ++el) {
      out << " & e" << el << ' ' << (con.elements.contains (el) ? "" : "/")
	  << ": c" << con.own_number;
    }
  }
  return out;
}

std::string compare (Constant *first_const, Constant *second_const, std::mt19937 &mt) {
  std::uniform_real_distribution<> distr {0, 1};
  double guess {distr (mt)};
  if (guess > first_const->threshold) {
    int possibilities {13};

    guess = guess - first_const->threshold;
    int comp {(int) (0.5 + guess * (1 / (1 - first_const->threshold)) * possibilities)};

    auto comparison_str
      { [] (Constant *first, Constant *second, std::string comparison) {
	return 'c' + std::to_string (first->own_number) + ' ' + comparison + " c" + std::to_string (second->own_number);
      }};

    auto disj
      { [&comparison_str] (Constant *first, Constant *second, bool pos = true) {
	return comparison_str (first, second, "/\\") + ' ' + (pos ? "" : "/") + "= {}";
      }};

    auto ovlp
      { [&comparison_str] (Constant *first, Constant *second, bool almost_neg = false) {
	if (almost_neg)
	  { return comparison_str (first, second, "\\/") + " = c" + std::to_string (first->own_number); }
	return comparison_str (first, second, "/\\") + " /= {} & "
	  + comparison_str (first, second, "-") + " /= {} & "
	  + comparison_str (second, first, "-") + " /= {}";
      }};
    
    std::string output;
    switch (comp) {
    case 0:
      output = comparison_str (first_const, second_const, "<:");
      break;
    case 1:
      output = comparison_str (first_const, second_const, "/<:");
      break;
    case 2:
      output = comparison_str (second_const, first_const, "<:");
      break;
    case 3:
      output = comparison_str (second_const, first_const, "/<:");
      break;
    case 4:
      output = comparison_str (first_const, second_const, "<<:");
      break;
    case 5:
      output = comparison_str (first_const, second_const, "/<<:");
      break;
    case 6:
      output = comparison_str (second_const, first_const, "<<:");
      break;
    case 7:
      output = comparison_str (second_const, first_const, "/<<:");
      break;
    case 8:
      output = comparison_str (first_const, second_const, "=");
      break;
    case 9:
      output = comparison_str (first_const, second_const, "=");
      break;
    case 10:
      output = disj (first_const, second_const);
      break;
    case 11:
      output = disj (first_const, second_const, false);
      break;
    case 12:
      output = ovlp (first_const, second_const);
      break;
    case 13:
      output = ovlp (first_const, second_const, true);
      break;
    }
    return output; 
  }
  return "";
}
  
int main (int argc, char **argv) {
  
  std::string machine_name;
  unsigned int seed {0};
  int set_count {0};

  auto usage { [] () {
    std::cerr << "Usage: ./rand_mch_gen -o <machine_name> -c <pos_number_of_sets> [-s <rand_num_seed>]\n";
    return 1;
  }};
  
  for (int i {1}; i < argc; ++i) {
    if (argv[i][0] == '-') {
      switch (argv[i][1]) {
      case 'o':
	machine_name = argv[++i];
	break;
      case 's':
	seed = std::stoi (argv[++i]);
	break;
      case 'c':
	set_count = std::stoi (argv[++i]);
	break;
      default:
	return usage ();
      }
    }
    else
      { return usage (); }
  }

  if (machine_name.empty () || set_count <= 0)
    { return usage (); }

  if (seed == 0)
    { seed = std::chrono::steady_clock::now ().time_since_epoch ().count (); }

  std::mt19937 rng {seed};

  std::vector<Constant *> sets (set_count);
  
  for (int i {0}; i < set_count; ++i) 
    { sets[i] = new Constant {rng, set_count, i}; }
  
  std::stringstream pog;
  pog << "// Set count: " << set_count
      << "\n// Seed: " << seed
      << "\nMACHINE\n    " << machine_name << "\n\n";

  pog << "CONSTANTS\n    c" << 0;
  for (int i {1}; i < set_count; ++i)
    { pog << ", c" << i; }
  for (int el {0}; el <= set_count; ++el) 
    { pog << ", e" << el; }

  pog << "\n\nPROPERTIES\n    e0 : NAT";
  for (int i {1}; i <= set_count; ++i)
    { pog << " & e" << i << " : NAT"; }
  for (int i {0}; i < set_count; ++i)
    { pog << " &\n    " << *sets[i]; }

  pog << "\n\nASSERTIONS\n    ";

  bool started {false};
  
  for (auto first {sets.begin ()}; first != std::prev (sets.end ()); ++first) {
    for (auto second {std::next (first)}; second != sets.end (); ++second) {
      std::string output {compare (*first, *second, rng)};
      if (!output.empty ()) {
	if (started)
	  { pog << " &\n    "; }
	else
	  { started = true; }

	pog << output;
      }
    }
  }

  pog << "\n\nEND\n";

  std::ofstream machine {machine_name + ".mch"};
  machine << pog.str ();

  std::cout << sets[0]->threshold << '\n';
  for (auto el : sets)
    { delete el; }
  
  return 0;
}
