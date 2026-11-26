// Independent check of the variable-length ternary (8,6) optimum.
// Build with a C++20 compiler. No external libraries or input files.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

namespace {
constexpr int maxLength = 8, minDistance = 6;
using Bits = std::vector<std::uint64_t>;

int editDistance(const std::string& a, const std::string& b) {
    std::array<int, maxLength + 1> row{};
    const int m = static_cast<int>(b.size());
    for (int j = 0; j <= m; ++j) row[j] = j;
    for (char x : a) {
        int diagonal = row[0]++;
        for (int j = 1; j <= m; ++j) {
            const int above = row[j];
            row[j] = std::min({above + 1, row[j-1] + 1, diagonal + (x != b[j-1])});
            diagonal = above;
        }
    }
    return row[m];
}

void enumerate(const std::string& prefix, std::vector<std::string>& words) {
    if (prefix.size() >= minDistance) words.push_back(prefix);
    if (prefix.size() == maxLength) return;
    for (char letter : std::string("012")) enumerate(prefix + letter, words);
}

class CompatibilityGraph {
public:
    explicit CompatibilityGraph(const std::vector<std::string>& words)
        : blocks((words.size() + 63) / 64), rows(words.size(), Bits(blocks)) {
        for (std::size_t i = 0; i < words.size(); ++i) {
            for (std::size_t j = i + 1; j < words.size(); ++j) {
                if (editDistance(words[i], words[j]) < minDistance) continue;
                rows[i][j/64] |= std::uint64_t{1} << (j%64);
                rows[j][i/64] |= std::uint64_t{1} << (i%64);
                ++edgeCount;
            }
        }
    }

    bool adjacent(int i, int j) const { return (rows[i][j/64] >> (j%64)) & 1; }

    // Candidates are later than all choices made in this recursive call chain.
    bool extend(const std::vector<int>& candidates, int need, std::vector<int>& clique) const {
        if (need == 0) return true;
        for (std::size_t i = 0; i + need <= candidates.size(); ++i) {
            const int v = candidates[i];
            std::vector<int> next;
            for (std::size_t j = i+1; j < candidates.size(); ++j)
                if (adjacent(v, candidates[j])) next.push_back(candidates[j]);
            if (static_cast<int>(next.size()) < need-1) continue;
            clique.push_back(v);
            if (extend(next, need-1, clique)) return true;
            clique.pop_back();
        }
        return false;
    }

    std::size_t blocks;
    std::vector<Bits> rows;
    std::uint64_t edgeCount = 0;
};

template <class F>
void forEachBit(std::uint64_t bits, std::size_t block, F visit) {
    while (bits) {
        visit(static_cast<int>(64*block + std::countr_zero(bits)));
        bits &= bits-1;
    }
}
} // namespace

int main() {
    const std::vector<std::string> witness{
        "", "000000", "00111111", "00222222", "11001122", "11120201", "22002211", "22210102"};
    int minimum = maxLength + 1, longest = 0;
    for (std::size_t i = 0; i < witness.size(); ++i) {
        longest = std::max(longest, static_cast<int>(witness[i].size()));
        if (witness[i].size() > maxLength || witness[i].find_first_not_of("012") != std::string::npos)
            return 1;
        for (std::size_t j = 0; j < i; ++j)
            minimum = std::min(minimum, editDistance(witness[i], witness[j]));
    }
    if (witness.size() != 8 || minimum != minDistance || longest != maxLength) return 1;
    std::cout << "Witness: 8 words, maximum length " << longest << ", minimum distance " << minimum << '\n';

    std::vector<std::string> words;
    enumerate("", words);
    const CompatibilityGraph g(words);
    std::cout << "Long-word graph: " << words.size() << " vertices, " << g.edgeCount << " edges\n";

    // Eight long words have a triple with one initial letter. A simultaneous
    // permutation of the alphabet sends that letter to 0 and preserves every distance.
    std::vector<int> zero;
    Bits firstZero(g.blocks), pair(g.blocks);
    for (int v = 0; v < static_cast<int>(words.size()); ++v) {
        if (words[v].front() != '0') continue;
        zero.push_back(v);
        firstZero[v/64] |= std::uint64_t{1} << (v%64);
    }
    std::uint64_t triples = 0;
    std::vector<int> clique;
    for (int a : zero) for (int b : zero) {
        if (b <= a || !g.adjacent(a,b)) continue;
        for (std::size_t j = 0; j < g.blocks; ++j) pair[j] = g.rows[a][j] & g.rows[b][j];
        for (std::size_t j = b/64; j < g.blocks; ++j) {
            bool found = false;
            forEachBit(pair[j] & firstZero[j], j, [&](int c) {
                if (c <= b || found) return;
                ++triples;
                std::vector<int> common;
                for (std::size_t t = 0; t < g.blocks; ++t)
                    forEachBit(pair[t] & g.rows[c][t], t, [&](int v) { common.push_back(v); });
                clique = {a,b,c};
                found = g.extend(common, 5, clique);
            });
            if (found) {
                std::cerr << "Found an eight-vertex clique:";
                for (int v : clique) std::cerr << ' ' << words[v];
                std::cerr << '\n';
                return 1;
            }
        }
    }
    std::cout << "First-letter-0 triples exhausted: " << triples
              << "\nEight long words are impossible. Optimal code size: 8\n";
}
