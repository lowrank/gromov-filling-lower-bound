"""Fixed-profile quadrature for the strip comparison. Requires NumPy."""

import numpy as np


def test_profile(angles, profile):
    n = len(angles)
    multiplier = -1j*np.sign(np.fft.fftfreq(n))
    multiplier[n//2] = 0  # real periodic grid transform

    def hilbert(values):
        return np.fft.ifft(multiplier*np.fft.fft(values))

    u = np.arctanh(np.sin(profile))
    d_factor = 1/np.cos(profile)
    c_factor = np.cos(hilbert(u).real)
    assert np.min(c_factor) > 0
    phase = np.exp(1j*(angles+hilbert(np.log(d_factor*c_factor)).real/2))
    value = -np.mean((phase.conj()*c_factor*hilbert(d_factor*phase)).imag)
    upper = np.sqrt(np.mean(d_factor**2)*np.mean(c_factor**2))
    return value, upper


def main():
    budget = 2*np.pi/6.15
    fine_values = {}
    for n in (256, 512, 1024):
        angles = 2*np.pi*(np.arange(n)+0.5)/n
        round_three = np.arcsin(np.cos(3*angles)/3)
        value, upper = test_profile(angles, round_three)
        assert abs(upper-1) < 1e-12 and abs(value-1) < 1e-12
        boundary = np.pi/2-abs((angles+np.pi) % (2*np.pi)-np.pi)
        for width in (0.2, 0.05):
            eroded = np.sign(boundary)*np.maximum(abs(boundary)-width, 0)
            value, upper = test_profile(angles, eroded)
            print(f'{n:4d} labels  erosion {width:.2f}  test {value:.8f}  Cauchy majorant {upper:.8f}')
            if width == 0.05:
                fine_values[n] = value
    assert fine_values[512] < budget < fine_values[1024]
    print(f'6.15 normalization budget {budget:.8f}; grid values are numerical diagnostics.')


if __name__ == '__main__':
    main()
