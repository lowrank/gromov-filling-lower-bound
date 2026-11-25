// Exact acceptance of proposed Hermitian Gram factors on all terminal profiles.
#include <algorithm>
#include <cmath>
#include <complex>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif

namespace {
using I = std::int64_t;
using Wide = __int128;
using Z = std::complex<double>;
constexpr int max_n = 112;
constexpr I den = 64000000000000LL;
constexpr I scalar_den = 100000000;
constexpr I digits = 1000000000000LL;
constexpr I unit_d = 1000000000;
Wide magnitude(Wide a) { return a < 0 ? -a : a; }

struct IntegerPair { I re, im; };

struct Work {
    Z chol[max_n][max_n];
    IntegerPair factor[max_n][max_n], gram[max_n][max_n];
    int order[max_n], neighbors[max_n];
    I edge[max_n][max_n];
    Wide energy[max_n], allowance[max_n];

    void assemble(int n, int bins, const std::uint8_t* box, const std::int32_t* index,
                  const I* coefficient) {
        for (int i = 0; i < n; ++i) order[i] = i;
        std::sort(order, order+n, [&](int i, int j) {
            const int a = std::min<int>(box[i],bins-1-box[i]);
            const int b = std::min<int>(box[j],bins-1-box[j]);
            return a == b ? i < j : a > b;
        });
        for (int i = 0; i < n; ++i) for (int j = 0; j < i; ++j) {
            const int a = order[i], b = order[j], l = std::min(a,b), r = std::max(a,b);
            const int id = index[((r-l)*bins+box[l])*bins+box[r]];
            if (id < 0) throw std::runtime_error("missing compatible pair class");
            // The raw coefficient has denominator 16e12; here we need iW/2 in units of 1/den.
            edge[i][j] = (a < b ? 2 : -2)*coefficient[id];
        }
    }

    bool positive(int n, const I* d, double shift) {
        const I largest = *std::max_element(d,d+n);
        const I scale = I(1) << (largest < den/5 ? 32 : largest < den*9/10 ? 31 : 30);
        const Wide scale2 = Wide(scale)*scale;
        for (int i = 0; i < n; ++i) {
            chol[i][i] = double(d[order[i]])/den - shift;
            for (int j = 0; j < i; ++j) chol[i][j] = Z(0,double(edge[i][j])/den);
            energy[i] = 0;
        }
        // Floating point only proposes a sparse factor. Acceptance below uses integers.
        for (int k = 0; k < n; ++k) {
            const double pivot = chol[k][k].real();
            if (!(pivot > 0)) return false;
            const double root = std::sqrt(pivot);
            chol[k][k] = root;
            int used = 0;
            for (int i = k+1; i < n; ++i) {
                if (chol[i][k] != Z(0,0)) {
                    neighbors[used++] = i;
                    chol[i][k] /= root;
                }
            }
            for (int p = 0; p < used; ++p) {
                const int i = neighbors[p];
                chol[i][i] -= std::norm(chol[i][k]);
                if (!(chol[i][i].real() > 0)) return false;
                for (int q = p+1; q < used; ++q) {
                    const int j = neighbors[q];
                    chol[j][i] -= chol[j][k]*std::conj(chol[i][k]);
                }
            }
        }
        for (int i = 0; i < n; ++i) for (int k = 0; k <= i; ++k) {
            const Z a = chol[i][k]*double(scale);
            if (!(std::abs(a.real()) < 3.e9 && std::abs(a.imag()) < 3.e9)) return false;
            const I x = std::llround(a.real()), y = std::llround(a.imag());
            factor[i][k] = {x,y};
            gram[i][k] = {0,0};
            energy[i] += Wide(x)*x+Wide(y)*y;
        }
        // Cauchy-Schwarz bounds every real or imaginary partial dot product,
        // including the sum of absolute products, by sqrt(energy[i]*energy[j]).
        for (int i = 0; i < n; ++i)
            if (energy[i] > std::numeric_limits<I>::max()/2) return false;
        for (int k = 0; k < n; ++k) {
            int used = 0;
            for (int i = k; i < n; ++i)
                if (factor[i][k].re || factor[i][k].im) neighbors[used++] = i;
            for (int p = 0; p < used; ++p) {
                const int i = neighbors[p];
                const auto a = factor[i][k];
                for (int q = 0; q < p; ++q) {
                    const int j = neighbors[q];
                    const auto b = factor[j][k];
                    gram[i][j].re += a.re*b.re+a.im*b.im;
                    gram[i][j].im += a.im*b.re-a.re*b.im;
                }
            }
        }
        for (int i = 0; i < n; ++i) allowance[i] = Wide(d[order[i]])*scale2-den*energy[i];
        for (int i = 0; i < n; ++i) for (int j = 0; j < i; ++j) {
            const Wide cost = magnitude(Wide(den)*gram[i][j].re) +
                              magnitude(Wide(edge[i][j])*scale2-Wide(den)*gram[i][j].im);
            allowance[i] -= cost;
            allowance[j] -= cost;
        }
        return std::all_of(allowance,allowance+n,[](Wide a){ return a >= 0; });
    }

    bool accept(int n, const std::uint8_t* cells, const std::int32_t* sigma, const I* d, I cap) {
        const Wide budget = Wide(cap)*(den/digits)*scalar_den*scalar_den;
        Wide sum = 0;
        for (int i = 0; i < n; ++i) {
            if (d[i] < 0 || d[i] > 2*den) return false;
            const I s = sigma[cells[i]];
            const Wide weight = Wide(d[i])*s*s;
            if (Wide(16)*n*weight < budget) return false;
            sum += weight;
        }
        // den is divisible by digits, so every multiplication fits the checked input ranges.
        if (sum > budget) return false;
        return positive(n,d,1.2e-8) || positive(n,d,3.e-9);
    }
};

template<class T> std::vector<T> read(std::istream& f, size_t n) {
    std::vector<T> v(n);
    if (!f.read(reinterpret_cast<char*>(v.data()),n*sizeof(T))) throw std::runtime_error("short binary input");
    return v;
}
}

// Return the indices of failed rows through status. A nonnegative status certifies that row.
extern "C" void free_psd(int rows, int n, int bins, I cap, [[maybe_unused]] int threads, const std::uint8_t* boxes,
                         const std::int32_t* index, const I* w, const std::int32_t* sigma,
                         const I* old, const std::int32_t* witness_id, const std::uint32_t* witnesses,
                         std::int32_t* status) {
#ifdef _OPENMP
#pragma omp parallel num_threads(threads)
#endif
    {
        Work work;
#ifdef _OPENMP
#pragma omp for schedule(dynamic,24)
#endif
        for (int p = 0; p < rows; ++p) {
            const auto* box = boxes+size_t(p)*n;
            const auto* ref = old+size_t(p)*n;
            I d[max_n];
            work.assemble(n,bins,box,index,w);
            status[p] = -1;
            if (witness_id[p] >= 0) {
                const auto* supplied = witnesses+size_t(witness_id[p])*n;
                for (int i = 0; i < n; ++i) d[i] = I(supplied[i])*(den/unit_d);
                if (work.accept(n,box,sigma,d,cap)) status[p] = 3;
                continue;
            }
            double original[max_n], total = 0;
            for (int i = 0; i < n; ++i) {
                const double s = double(sigma[box[i]])/scalar_den;
                original[i] = double(ref[i])/den*s*s;
                total += original[i];
            }
            if (!(total > 0)) continue;
            const double room = double(cap)/digits-2.e-9-total;
            const double proportions[] = {.25,.85,0.};
            for (int pass = 0; pass < 3; ++pass) {
                const double share = proportions[pass];
                bool valid = true;
                for (int i = 0; i < n; ++i) {
                    const double s = double(sigma[box[i]])/scalar_den;
                    const double val = (original[i]+room*((1-share)/n+share*original[i]/total))*den/(s*s);
                    if (!(val >= 0 && val <= 2*den)) { valid = false; break; }
                    d[i] = I(std::floor(val));
                }
                if (valid && work.accept(n,box,sigma,d,cap)) { status[p] = pass; break; }
            }
        }
    }
}

#ifndef ISSUE163_LIBRARY
int main(int argc, char** argv) try {
    if (argc == 2 && std::string(argv[1]) == "--check-runtime") return 0;
    if (argc != 3) throw std::runtime_error("expected input and witness paths");
    std::uint32_t endian = 1;
    if (*reinterpret_cast<std::uint8_t*>(&endian) != 1) throw std::runtime_error("little-endian input required");
    std::ifstream f(argv[1],std::ios::binary), cert(argv[2],std::ios::binary);
    auto head = read<std::int32_t>(f,4);
    const int n = head[0], bins = head[1], rows = head[2], classes = head[3];
    const I cap = read<I>(f,1)[0];
    if ((n!=14 && n!=28 && n!=56 && n!=112) || bins<=0 || bins>112 || rows<=0 || rows>120000 ||
        classes<=0 || classes>70000 || cap<=0 || cap>2*digits) throw std::runtime_error("invalid dimensions or budget");
    auto box = read<std::uint8_t>(f,size_t(rows)*n);
    auto idx = read<std::int32_t>(f,n*bins*bins);
    auto w = read<I>(f,classes);
    auto s = read<std::int32_t>(f,bins);
    auto d = read<I>(f,size_t(rows)*n);
    if (f.peek()!=EOF || std::any_of(box.begin(),box.end(),[=](int x){return x>=bins;}) ||
        std::any_of(idx.begin(),idx.end(),[=](int x){return x< -1 || x>=classes;}) ||
        std::any_of(w.begin(),w.end(),[](I x){return magnitude(x)>den;}) ||
        std::any_of(s.begin(),s.end(),[](int x){return x<=0 || x>2*scalar_den;}) ||
        std::any_of(d.begin(),d.end(),[](I x){return x<0 || x>2*den;}))
        throw std::runtime_error("invalid finite data");
    const auto count = read<std::uint32_t>(cert,1)[0];
    if (count>unsigned(rows)) throw std::runtime_error("witness count");
    auto ids = read<std::uint32_t>(cert,count);
    auto data = read<std::uint32_t>(cert,size_t(count)*n);
    if (cert.peek()!=EOF) throw std::runtime_error("trailing witness data");
    std::vector<std::int32_t> pos(rows,-1), status(rows);
    for (unsigned k = 0; k<count; ++k) {
        if (ids[k]>=unsigned(rows) || pos[ids[k]]>=0) throw std::runtime_error("witness index");
        pos[ids[k]]=k;
    }
    free_psd(rows,n,bins,cap,3,box.data(),idx.data(),w.data(),s.data(),d.data(),pos.data(),data.data(),status.data());
    const auto bad = std::find(status.begin(),status.end(),-1);
    if (bad!=status.end()) throw std::runtime_error("uncertified row at level "+std::to_string(n)+", index "+std::to_string(bad-status.begin()));
    std::cout << n << " anchors, " << rows << " exact PSD checks, " << count
              << " supplied diagonals, normalized diagonal floor 1/(16n)\n";
    return 0;
} catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
#endif
