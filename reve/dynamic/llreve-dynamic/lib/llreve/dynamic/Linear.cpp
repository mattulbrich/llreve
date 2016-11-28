/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/Linear.h"

#include <gmpxx.h>

using std::vector;

// This is not completely reduced as the leading entries are not normalized
void reducedRowEchelonForm(Matrix<mpq_class> &input) {
    size_t currentRow = 0;
    for (size_t currentCol = 0; currentCol < input.at(0).size(); ++currentCol) {
        // Find non-zero entry in this column
        int64_t nonZeroRow = -1;
        for (size_t i = currentRow; i < input.size(); ++i) {
            if (input[i][currentCol] != mpq_class(0)) {
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
            swap(input[static_cast<size_t>(nonZeroRow)], input[currentRow]);
        }
        // Subtract the current row from the rows above it
        for (size_t i = 0; i < currentRow; ++i) {
            mpq_class multiple =
                input[i][currentCol] / input[currentRow][currentCol];
            for (size_t j = currentCol; j < input[i].size(); ++j) {
                input[i][j] -= multiple * input[currentRow][j];
            }
        }
        // Subtract the current row from the rows below it
        for (size_t i = currentRow + 1; i < input.size(); ++i) {
            mpq_class multiple =
                input[i][currentCol] / input[currentRow][currentCol];
            for (size_t j = currentCol; j < input[i].size(); ++j) {
                input[i][j] -= multiple * input[currentRow][j];
            }
        }
        ++currentRow;
    }
}

// Checks if newVector is linearly indepentent of vectors. vectors has to be in
// reduced row echelon form
bool linearlyIndependent(const Matrix<mpq_class> &vectors,
                         vector<mpq_class> newVector) {
    if (vectors.empty()) {
        return true;
    }
    assert(newVector.size() == vectors[0].size());
    size_t col = 0;
    for (size_t row = 0; row < vectors.size(); ++row) {
        // We don’t allow zero rows so we don’t need a bounds check here
        while (vectors[row][col] == 0) {
            if (newVector[col] != 0) {
                return true;
            } else {
                ++col;
            }
        }
        assert(col < vectors[row].size());
        assert(vectors[row][col] != 0);
        mpq_class multiple = newVector[col] / vectors[row][col];
        for (size_t newVecCol = col; newVecCol < newVector.size();
             ++newVecCol) {
            newVector[newVecCol] -= multiple * vectors[row][newVecCol];
        }
        assert(newVector[col] == 0);
        ++col;
    }
    for (const auto &i : newVector) {
        if (i != 0) {
            return true;
        }
    }
    return false;
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
    Matrix<mpq_class> rowEchelon = m;
    reducedRowEchelonForm(rowEchelon);
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
