#! /usr/bin/env python3
import numpy
import scipy.stats
import matplotlib.pyplot as plot

V = 50


def show_scaled_grades(average, target_average, samples=100):
    assert 0 <= average <= 1.0
    assert 0 <= target_average <= 1.0
    alpha = average * V
    beta = (1 - average) * V
    raw_grades = numpy.random.default_rng().beta(alpha, beta, samples)

    fig, axs = plot.subplots(2, 1, sharex=True)

    _, raw_bins, _ = axs[0].hist(raw_grades, bins=10, density=True, label='raw grades')
    raw_pdf = scipy.stats.beta.pdf(raw_bins, alpha, beta)
    axs[0].plot(raw_bins, raw_pdf, label='raw pdf')

    if average <= target_average:
        curved_grades = 1.0 - (1.0 - raw_grades) * (
            (1.0 - target_average) / (1.0 - average)
        )

        _, curved_bins, _ = axs[1].hist(curved_grades, bins=10, density=True, label='curved_grades')
        curved_pdf = scipy.stats.beta.pdf(
            curved_bins, target_average * V, (1 - target_average) * V
        )
        axs[1].plot(curved_bins, curved_pdf, label='curved pdf')

    fig.legend()
    plot.show()


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(description='plot grades and curve distribution')
    p.add_argument('-t', '--target', type=float, default=0.85, help='target average')
    p.add_argument('-s', '--samples', type=int, default=100, help='number samples')
    p.add_argument('average', type=float, help='raw average')

    args = p.parse_args()
    show_scaled_grades(args.average, args.target, args.samples)
