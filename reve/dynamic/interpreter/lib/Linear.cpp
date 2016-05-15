#include "Linear.h"

#include <gmpxx.h>

using std::vector;

Matrix<mpq_class> rowEchelonForm(Matrix<mpq_class> input) {
    size_t currentRow = 0;
    for (size_t currentCol = 0; currentCol < input.at(0).size(); ++currentCol) {
        // Find non-zero entry in this column
        int64_t nonZeroRow = -1;
        for (size_t i = currentRow; i < input.size(); ++i) {
            if (input.at(i).at(currentCol) != mpq_class(0)) {
                nonZeroRow = static_cast<int64_t>(i);
                break;
            }
        }
        if (nonZeroRow == -1) {
            // No non zero entry
            continue;
        }
        if (static_cast<size_t>(nonZeroRow) != currentRow) {
            // Swap rows
            swap(input.at(static_cast<size_t>(nonZeroRow)),
                 input.at(currentRow));
        }
        for (size_t i = currentRow + 1; i < input.size(); ++i) {
            mpq_class multiple = input.at(i).at(currentCol) /
                                 input.at(currentRow).at(currentCol);
            for (size_t j = currentCol; j < input.at(i).size(); ++j) {
                input.at(i).at(j) -= multiple * input.at(currentRow).at(j);
            }
        }
        ++currentRow;
    }
    return input;
}

size_t rank(const Matrix<mpq_class> &m) {
    const Matrix<mpq_class> rowEchelon = rowEchelonForm(m);
    int64_t i = static_cast<int64_t>(rowEchelon.size()) - 1;
    while (i >= 0 && isZero(rowEchelon.at(static_cast<size_t>(i)))) {
        --i;
    }
    return static_cast<size_t>(i + 1);
}

bool linearlyIndependent(const vector<vector<mpq_class>> &vectors) {
    size_t rows = vectors.at(0).size();
    Matrix<mpq_class> m(rows);
    for (size_t row = 0; row < vectors.at(0).size(); ++row) {
        for (const auto &vec : vectors) {
            m.at(row).push_back(vec.at(row));
        }
    }
    return rank(m) == vectors.size();
}

vector<mpq_class> multiplyRow(vector<mpq_class> vec, mpq_class c) {
    for (auto &entry : vec) {
        entry *= c;
    }
    return vec;
}

vector<vector<mpq_class>> nullSpace(const Matrix<mpq_class> &m) {
    if (m.empty()) {
        // Not sure if this is correct mathematically but it’s the sensible
        // thing to do here
        return {};
    }
    assert(m.at(0).size() >= m.size());
    Matrix<mpq_class> rowEchelon = rowEchelonForm(m);
    for (size_t row = 0; row < rowEchelon.size(); ++row) {
        size_t col = 0;
        while (rowEchelon.at(row).at(col) == 0) {
            col++;
        }
        if (col < rowEchelon.at(row).size()) {
            rowEchelon.at(row) =
                multiplyRow(rowEchelon.at(row), 1 / rowEchelon.at(row).at(col));
            for (size_t i = 0; i < row; ++i) {
                mpq_class multiple = rowEchelon.at(i).at(col);
                for (size_t j = col; j < rowEchelon.at(i).size(); ++j) {
                    rowEchelon.at(i).at(j) -=
                        multiple * rowEchelon.at(row).at(j);
                }
            }
        }
    }
    vector<mpq_class> zero(m.at(0).size());
    Matrix<mpq_class> full(zero.size(), zero);
    for (const auto &row : rowEchelon) {
        // Find first non zero entry
        size_t i = 0;
        while (row.at(i) == 0) {
            ++i;
        }
        if (i != full.size()) {
            full.at(i) = row;
        }
    }
    vector<vector<mpq_class>> nullSpaceBasis;
    for (size_t i = 0; i < full.size(); ++i) {
        if (full.at(i).at(i) == 0) {
            vector<mpq_class> basisVector(full.size(), 0);
            for (size_t k = 0; k < i; ++k) {
                basisVector.at(k) = full.at(k).at(i);
            }
            basisVector.at(i) = -1;
            nullSpaceBasis.push_back(basisVector);
        }
    }
    return nullSpaceBasis;
}

vector<mpz_class> ratToInt(vector<mpq_class> vec) {
    mpz_class leastCommonMultiple = vec.at(0).get_den();
    for (size_t i = 1; i < vec.size(); ++i) {
        leastCommonMultiple = lcm(leastCommonMultiple, vec.at(i).get_den());
    }
    vector<mpz_class> output(vec.size());
    for (size_t i = 0; i < vec.size(); ++i) {
        output.at(i) =
            vec.at(i).get_num() * (leastCommonMultiple / vec.at(i).get_den());
    }
    mpz_class greatestCommonDivisor = output.at(0);
    for (size_t i = 1; i < output.size(); ++i) {
        greatestCommonDivisor = gcd(greatestCommonDivisor, output.at(i));
    }
    for (auto &entry : output) {
        entry /= greatestCommonDivisor;
    }
    return output;
}
