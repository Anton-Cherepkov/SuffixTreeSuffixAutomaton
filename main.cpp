#include <iostream>
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <cassert>
#include <limits>

template <char MIN_CHAR, char MAX_CHAR>
class SuffixAutomaton {
protected:
    const static size_t ALPHABET_SIZE = MAX_CHAR - MIN_CHAR + static_cast<size_t>(1);
    struct Node {
        int transition[ALPHABET_SIZE];
        int suffixLink;
        size_t maximumLength;

        bool isTerminal;
        size_t numberOfEntries;

        Node() : suffixLink(-1), maximumLength(0), isTerminal(false), numberOfEntries(1) {
            std::fill(transition, transition + ALPHABET_SIZE, -1);
        }
    };

    std::vector<Node> nodes;
    size_t nodesUsed;
    size_t finishState;

private:
    void initialize(size_t strLength) {
        nodes.resize((strLength + 1) << 2);
        nodes[0].numberOfEntries = 0;
        nodesUsed = 1;
        finishState = 0;
    }

    size_t getNewNode() {
        return nodesUsed++;
    }

    size_t getClonedNode(size_t cloneOf) {
        size_t clone = getNewNode();
        std::copy(nodes[cloneOf].transition, nodes[cloneOf].transition + ALPHABET_SIZE, nodes[clone].transition);
        nodes[clone].suffixLink = nodes[cloneOf].suffixLink;
        nodes[clone].maximumLength = nodes[cloneOf].maximumLength;
        nodes[clone].isTerminal = nodes[cloneOf].isTerminal;
        nodes[clone].numberOfEntries = 0;
        return clone;
    }

    /*
     * symbol must belong to range [0; ALPHABET_SIZE)
     */
    void appendSymbol(unsigned char symbol) {
        size_t newNode = getNewNode();
        nodes[newNode].maximumLength = nodes[finishState].maximumLength + 1;

        int i = finishState;
        finishState = newNode;

        while (i != -1 && nodes[i].transition[symbol] == -1) {
            nodes[i].transition[symbol] = newNode;
            i = nodes[i].suffixLink;
        }

        if (i == -1) {
            nodes[newNode].suffixLink = 0;
            return;
        }

        assert(nodes[i].transition[symbol] != -1);
        int j = nodes[i].transition[symbol];

        if (nodes[j].maximumLength == nodes[i].maximumLength + 1) {
            nodes[newNode].suffixLink = j;
            return;
        }

        size_t clone = getClonedNode(j);
        nodes[clone].maximumLength = nodes[i].maximumLength + 1;
        nodes[j].suffixLink = clone;
        nodes[newNode].suffixLink = clone;

        while (i != -1 && nodes[i].transition[symbol] == j) {
            nodes[i].transition[symbol] = clone;
            i = nodes[i].suffixLink;
        }
    }

    void markTerminalNodes() {
        int i = finishState;
        while (i != -1) {
            nodes[i].isTerminal = true;
            i = nodes[i].suffixLink;
        }
    }

    void calculateNumbersOfEntries() {
        std::vector<size_t> vec(nodesUsed - 1);
        for (size_t i = 1; i < nodesUsed; ++i) {
            vec[i - 1] = i;
        }
        std::sort(vec.begin(), vec.end(), [this] (size_t a, size_t b) {
            return nodes[a].maximumLength > nodes[b].maximumLength;
        });
        for (auto node: vec) {
            nodes[nodes[node].suffixLink].numberOfEntries += nodes[node].numberOfEntries;
        }
    }

public:
    SuffixAutomaton() = delete;

    /*
     * str must contain characters from range [MIN_CHAR; MAX_CHAR]
     */
    explicit SuffixAutomaton(const std::string& str) {
        initialize(str.length());
        for (auto symbol: str) {
            appendSymbol(static_cast<unsigned char>(symbol - MIN_CHAR));
        }
        markTerminalNodes();
        calculateNumbersOfEntries();
    }

};

template <char MIN_CHAR, char MAX_CHAR>
class SuffixTree {
protected:
    const static size_t ALPHABET_SIZE = MAX_CHAR - MIN_CHAR + static_cast<size_t>(2);
    const static size_t INF = std::numeric_limits<size_t>::max() / 2;

    std::string str;
    struct Node {
        int transition[ALPHABET_SIZE];
        int suffixLink;
        int parent;

        size_t left;
        size_t length;

        Node() = delete;
        explicit Node(size_t left, size_t length) : suffixLink(-1), parent(-1), left(left), length(length) {
            std::fill(transition, transition + ALPHABET_SIZE, -1);
        }
    };

    std::vector<Node> nodes;

    size_t getNewNode(size_t left, size_t length) {
        nodes.push_back(Node(left, length));
        return nodes.size() - 1;
    }

    void setChild(size_t parent, size_t child, unsigned char symbol) {
        nodes[parent].transition[symbol] = child;
        nodes[child].parent = parent;
    }

    char getChar(size_t node, size_t edgePosition) const {
        assert(node != root);
        assert(edgePosition < nodes[node].length);
        return str[nodes[node].left + edgePosition];
    }

    bool canGo(size_t node, size_t edgePosition, unsigned char symbol) const {
        if (edgePosition + 1 < nodes[node].length) {
            return getChar(node, edgePosition + 1) == symbol;
        }
        return nodes[node].transition[symbol] != -1;
    }

    size_t splitEdge(size_t node, size_t edgePosition) {
        assert(edgePosition + 1 < nodes[node].length);

        size_t newNode = getNewNode(nodes[node].left, edgePosition + 1);

        size_t oldParent = nodes[node].parent;
        setChild(oldParent, newNode, str[nodes[node].left]);
        setChild(newNode, node, str[nodes[node].left + edgePosition + 1]);

        nodes[node].left += edgePosition + 1;
        if (nodes[node].length != INF) {
            nodes[node].length -= edgePosition + 1;
        }

        return newNode;
    }

    size_t getSuffixLink(size_t node) {
        if (nodes[node].suffixLink == -1) {
            int currentNode = nodes[nodes[node].parent].suffixLink;
            assert(currentNode != -1);
            size_t nextSymbolIndex = nodes[node].left;
            size_t symbolsRemain = nodes[node].length;
            unsigned char nextSymbol;

            while (true) {
                if (symbolsRemain == 0) {
                    break;
                }
                nextSymbol = static_cast<unsigned char>(str[nextSymbolIndex]);
                int nextNode = nodes[currentNode].transition[nextSymbol];
                assert(nextNode != -1);
                if (symbolsRemain < nodes[nextNode].length) {
                    break;
                }
                nextSymbolIndex += nodes[nextNode].length;
                symbolsRemain -= nodes[nextNode].length;
                currentNode = nextNode;
            }

            if (symbolsRemain == 0) {
                nodes[node].suffixLink = currentNode;
            } else {
                nextSymbol = static_cast<unsigned char>(str[nextSymbolIndex]);
                nodes[node].suffixLink = splitEdge(nodes[currentNode].transition[nextSymbol], symbolsRemain - 1);
            }

        }
        return nodes[node].suffixLink;
    }

    void initialize() {
        nodes.reserve(str.length() << 1);

        root = getNewNode(0, 0);
        size_t empty = getNewNode(0, 0);

        nodes[root].suffixLink = empty;
        nodes[root].length = 1;

        nodes[empty].length = 0;
        std::fill(nodes[empty].transition, nodes[empty].transition + ALPHABET_SIZE, root);

        activeNode = root;
        activeEdgePosition = 0;
    }

    size_t root;
    size_t activeNode;
    size_t activeEdgePosition;

    void addSymbol(unsigned char symbol, size_t pos) {
        while (true) {
            if (canGo(activeNode, activeEdgePosition, symbol)) {
                if (activeEdgePosition + 1 < nodes[activeNode].length) {
                    ++activeEdgePosition;
                } else {
                    assert(nodes[activeNode].transition[symbol] != -1);
                    activeNode = nodes[activeNode].transition[symbol];
                    activeEdgePosition = 0;
                }
                break;
            }
            if (activeEdgePosition + 1 < nodes[activeNode].length) {
                activeNode = splitEdge(activeNode, activeEdgePosition);
                assert(nodes[activeNode].length > 0);
                activeEdgePosition = nodes[activeNode].length - 1;
            }
            setChild(activeNode, getNewNode(pos, INF), symbol);
            activeNode = getSuffixLink(activeNode);
            activeEdgePosition = nodes[activeNode].length;
        }
    }

    void print(size_t v) const {
        if (v != root) {
            std::cout << (nodes[v].parent == root ? 1 : nodes[v].parent) << ' '
                      << v << ' '
                      << nodes[v].left + 1 << ' '
                      << std::min(nodes[v].left + nodes[v].length, str.length())
                      << '\n';
        }
        for (char symbol = 0; symbol < ALPHABET_SIZE; ++symbol) {
            if (nodes[v].transition[symbol] != -1) {
                print(nodes[v].transition[symbol]);
            }
        }
    }

public:
    SuffixTree() = delete;
    explicit SuffixTree(const std::string& str) : str(str) {
        initialize();
        this->str = str;
        for (size_t i = 0; i < this->str.size(); ++i) {
            assert(this->str[i] >= MIN_CHAR && this->str[i] <= MAX_CHAR);
            this->str[i] -= MIN_CHAR;
            addSymbol(static_cast<unsigned char>(this->str[i]), i);
        }
    }
    //~SuffixTree() = default;

    void print() const {
        std::cout << nodes.size() - 1 << ' ' << nodes.size() - 2 << '\n';
        print(root);
    }
};

class Refrain {
    std::vector<int> refrain;
    size_t numberOfEntries;

public:
    Refrain() = delete;
    Refrain(std::vector<int> refrain, size_t numberOfEntries) : refrain(std::move(refrain)), numberOfEntries(numberOfEntries) {}
    ~Refrain() = default;

    std::vector<int> getRefrain() const {
        return refrain;
    }

    size_t getNumberOfEntries() const {
        return numberOfEntries;
    }

    long long getMetrics() const {
        return static_cast<long long>(getNumberOfEntries()) * getRefrain().size();
    }

    void print(std::ostream& os) const {
        os << getMetrics() << '\n';
        os << refrain.size() << '\n';
        for (auto c: refrain) {
            os << c << ' ';
        }
    }
};

class SuffixAutomatonRefrainFinder : SuffixAutomaton<0, 10> {
    std::vector<std::pair<int, char>> longestParent;
    std::vector<char> dfsVisited;

    void calculateLongestParents(int node) {
        if (node == -1) {
            return;
        }

        dfsVisited[node] = 1;
        for (unsigned char symbol = 0; symbol < ALPHABET_SIZE; ++symbol) {
            int nextNode = nodes[node].transition[symbol];
            if (nextNode != -1 &&
                longestParent[nextNode].first == -1 &&
                nodes[nextNode].maximumLength == nodes[node].maximumLength + 1)
            {
                longestParent[nextNode].first = node;
                longestParent[nextNode].second = symbol;
            }
            if (!dfsVisited[nextNode]) {
                calculateLongestParents(nextNode);
            }
        }
    }

    Refrain findOnce() {
        longestParent.resize(nodesUsed, {-1, -1});
        dfsVisited.resize(nodesUsed, 0);
        calculateLongestParents(0);

        int best = 0;
        for (size_t i = 0; i < nodesUsed; ++i) {
            if (static_cast<long long>(nodes[i].maximumLength) * nodes[i].numberOfEntries >
                static_cast<long long>(nodes[best].maximumLength) * nodes[best].numberOfEntries)
            {
                best = i;
            }
        }

        size_t numberOfEntries = nodes[best].numberOfEntries;

        std::vector<int> refrain(nodes[best].maximumLength);
        for (int i = refrain.size() - 1; i >= 0; --i, best = longestParent[best].first) {
            refrain[i] = longestParent[best].second;
        }

        return Refrain(refrain, numberOfEntries);
    }

    static std::string getNormalizedString(const std::vector<int>& source) {
        std::string res(source.size(), 0);
        for (size_t i = 0; i < res.size(); ++i) {
            res[i] = (char)source[i];
        }
        return res;
    }

public:
    SuffixAutomatonRefrainFinder() = delete;
    explicit SuffixAutomatonRefrainFinder(const std::vector<int>& source) : SuffixAutomaton(getNormalizedString(source)) {}
    ~SuffixAutomatonRefrainFinder() = default;

    Refrain find() {
        static Refrain refrain = findOnce();
        longestParent.clear();
        dfsVisited.clear();
        longestParent.shrink_to_fit();
        dfsVisited.shrink_to_fit();
        return refrain;
    }
};

class SuffixTreeRefrainFinder : SuffixTree<0, 11> {
    static const char DOLLAR_SIGN = 11;

    std::vector<size_t> numberOfEntries;
    std::vector<size_t> lengths;
    std::vector<int> res;

    long long calcNumberOfEntries(int node) {
        if (node == -1) {
            return 0;
        }

        for (int child : nodes[node].transition) {
            numberOfEntries[node] += calcNumberOfEntries(child);
        }

        if (numberOfEntries[node] == 0) {
            numberOfEntries[node] = 1;
        }

        return numberOfEntries[node];
    }

    void calcLengths(int node, int currentLength = 0) {
        if (node != root) {
            currentLength += nodes[node].length;
        }

        bool isLeaf = true;
        for (int child: nodes[node].transition) {
            if (child != -1) {
                isLeaf = false;
                calcLengths(child, currentLength);
            }
        }

        if (isLeaf) {
            currentLength -= nodes[node].length; // give me my INF back
            currentLength += str.size() - nodes[node].left;
            currentLength -= 1; // throw away the '$'
        }
        lengths[node] = currentLength;
    }

    void restore(int node) {
        if (node == root) {
            return;
        }
        restore(nodes[node].parent);
        for (size_t i = 0; i < nodes[node].length && nodes[node].left + i < str.length(); ++i) {
            res.push_back(str[nodes[node].left + i]);
        }
    }

    Refrain findOnce() {
        numberOfEntries.resize(nodes.size(), 0);
        lengths.resize(nodes.size(), 0);

        calcNumberOfEntries(root);
        calcLengths(root);

        int best = 0;
        for (size_t node = 0; node < nodes.size(); ++node) {
            if (static_cast<long long>(lengths[node]) * numberOfEntries[node] >
                static_cast<long long>(lengths[best]) * numberOfEntries[best])
            {
                best = node;
            }
        }
        restore(best);
        bool isLeaf = true;
        for (auto child: nodes[best].transition) {
            if (child != -1) {
                isLeaf = false;
            }
        }
        if (isLeaf) {
            res.pop_back();
        }
        return Refrain(res, numberOfEntries[best]);
    }

    static std::string getNormalizedString(const std::vector<int>& source) {
        std::string res(source.size(), 0);
        for (size_t i = 0; i < res.size(); ++i) {
            res[i] = static_cast<char>(source[i]);
        }
        res.push_back(DOLLAR_SIGN);
        return res;
    }

public:
    SuffixTreeRefrainFinder() = delete;
    explicit SuffixTreeRefrainFinder(const std::vector<int>& source) : SuffixTree(getNormalizedString(source)) {}
    ~SuffixTreeRefrainFinder() = default;

    Refrain find() {
        static Refrain refrain = findOnce();
        numberOfEntries.clear();
        lengths.clear();
        res.clear();
        lengths.shrink_to_fit();
        res.shrink_to_fit();
        return refrain;
    }
};

int main() {
    std::ios_base::sync_with_stdio(false);
    size_t N, M;
    std::cin >> N >> M;
    std::vector<int> vec(N);
    for (size_t i = 0; i < N; ++i) {
        std::cin >> vec[i];
    }

    SuffixTreeRefrainFinder suffixTreeRefrainFinder(vec);
    SuffixAutomatonRefrainFinder suffixAutomatonRefrainFinder(vec);

    auto refrain1 = suffixAutomatonRefrainFinder.find();
    auto refrain2 = suffixTreeRefrainFinder.find();
    assert(refrain1.getMetrics() == refrain2.getMetrics());

    refrain1.print(std::cout);
    return 0;
}
