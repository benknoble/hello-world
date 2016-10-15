// //Ben Knoble's Project
using System.Collections.Generic;
using System.Collections;
using System.Linq;

namespace CollectionTypes
{
	/// <summary>
	/// An immutable, sorted collection of decimals representative of quantitative data points
	/// </summary>
	public class SingleVariableDataSet : IEnumerable<SingleVariableDataSet.DataPoint>, ICollection
	{
		readonly List<DataPoint> data;

		/// <summary>
		/// Initializes a new instance of the <see cref="SingleVariableDataSet"/> class
		/// by copying the values in data.
		/// </summary>
		/// <param name="data">Data</param>
		/// <exception cref="T:CollectionTypes.SingleVariableDataSet.EmptyDataSetException"></exception>
		public SingleVariableDataSet (List<DataPoint> data)
		{
			if (data.Count == 0)
				throw new EmptyDataSetException ($"{nameof (data)} is empty!");
			this.data = new List<DataPoint> (data);
			this.data = this.data.OrderBy (d => d.Value).ToList ();
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="SingleVariableDataSet"/> class
		/// with a string that is parsed into data.
		/// </summary>
		/// <param name="data">Data string in format acceptable to parser.</param>
		/// <param name="p">IParser that can parse the data.</param>
		/// <exception cref="T:CollectionTypes.SingleVariableDataSet.EmptyDataSetException"></exception>
		public SingleVariableDataSet (string data, IParser p)
		{
			this.data = new List<DataPoint> (p.ParseString (data));
			if (this.data.Count == 0)
				throw new EmptyDataSetException ($"{nameof (data)} contained no data points!");
			this.data = this.data.OrderBy (d => d.Value).ToList ();
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="SingleVariableDataSet"/> class
		/// with a variable number of DataPoints.
		/// </summary>
		/// <param name="data">Data.</param>
		/// <exception cref="T:CollectionTypes.SingleVariableDataSet.EmptyDataSetException"></exception>
		public SingleVariableDataSet (params DataPoint[] data)
		{
			if (data.Length == 0)
				throw new EmptyDataSetException ($"{nameof (data)} is empty!");
			this.data = data.ToList ();
			this.data = this.data.OrderBy (d => d.Value).ToList ();
		}

		SingleVariableDataSet ()
		{
		}

		/// <summary>
		/// Calculates the mean of the data set.
		/// </summary>
		/// <returns>Mean</returns>
		public decimal Mean ()
		{
			return data.Sum (d => d.Value) / data.Count;
		}

		/// <summary>
		/// Calculates the median of the data set.
		/// </summary>
		/// <returns>Median</returns>
		public DataPoint Median ()
		{
			return data.Count % 2 == 0
				? new DataPoint ((data[data.Count / 2].Value + data[data.Count / 2 + 1].Value) / 2)
				: data[data.Count / 2 + 1];
		}

		/// <summary>
		/// Calculates the minimum data point.
		/// </summary>
		/// <returns>Min</returns>
		public DataPoint Min ()
		{
			return data[0];//data.Min (d => d.Value)
		}

		/// <summary>
		/// Calculates the maximum data point.
		/// </summary>
		/// <returns>Max</returns>
		public DataPoint Max ()
		{
			return data[data.Count - 1];//data.Max (d => d.Value)
		}

		/// <summary>
		/// Calculates the first quartile.
		/// </summary>
		/// <returns>The first quartile.</returns>
		public DataPoint FirstQuartile ()
		{
			DataPoint median = Median ();
			var lowerhalf = new SingleVariableDataSet (new List<DataPoint> (data.FindAll (d => d < median)));
			return lowerhalf.Median ();
		}

		/// <summary>
		/// Calculates the third quartile.
		/// </summary>
		/// <returns>The third quartile.</returns>
		public DataPoint ThirdQuartile ()
		{
			DataPoint median = Median ();
			var upperhalf = new SingleVariableDataSet (new List<DataPoint> (data.FindAll (d => d > median)));
			return upperhalf.Median ();
		}

		/// <summary>
		/// Calculates the IQR.
		/// </summary>
		/// <returns>IQR.</returns>
		public decimal IQR ()
		{
			return ThirdQuartile () - FirstQuartile ();
		}

		/// <summary>
		/// Calculates the range.
		/// </summary>
		/// <returns>Range.</returns>
		public decimal Range ()
		{
			return Max () - Min ();
		}

		/// <summary>
		/// Calculates the frequency of the specified value.
		/// </summary>
		/// <returns>Frequency.</returns>
		/// <param name="value">Value.</param>
		public int Frequency (DataPoint value)
		{
			return data.Count (d => d.Value == value.Value);
		}

		/// <summary>
		/// Calculatest the relative frequency of the specified value.
		/// </summary>
		/// <returns>The relative frequency.</returns>
		/// <param name="value">Value.</param>
		public double RelativeFrequency (DataPoint value)
		{
			return Frequency (value) / data.Count;
		}

		/// <summary>
		/// Calculates the variance of the data.
		/// </summary>
		/// <returns>variance</returns>
		public double Variance ()
		{
			if (data.Count == 1)
				return 0;

			var mean = Mean ();

			return data.Sum (d => System.Math.Pow ((double)(d.Value - mean), 2)) / (data.Count - 1);
		}

		/// <summary>
		/// Calculates the standard deviation of the data
		/// </summary>
		/// <returns>The deviation.</returns>
		public double StandardDeviation ()
		{
			return System.Math.Sqrt (Variance ());
		}

		/// <summary>
		/// Calculates z-score.
		/// </summary>
		/// <returns>The z-score.</returns>
		/// <param name="value">Value.</param>
		public double ZScore (DataPoint value)
		{
			return (double)((value - Mean ()).Value) / StandardDeviation ();
		}

		/// <summary>
		/// Returns a copy of the backing list of DataPoints
		/// </summary>
		public List<DataPoint> Data ()
		{
			return new List<DataPoint> (data);
		}

		/// <summary>
		/// Transform the specified set of data d where each point => a + point.value * b
		/// </summary>
		/// <param name="d">SingleVariableDataSet</param>
		/// <param name="a">Constant added.</param>
		/// <param name="b">Constant multiplied.</param>
		public static SingleVariableDataSet LinearTransform (SingleVariableDataSet d, decimal a, decimal b)
		{
			var transformed2 = d.data.Select (point => new DataPoint (a + point.Value * b));
			var list = transformed2.ToList ();
			return new SingleVariableDataSet (list);
		}

		/// <summary>
		/// Transform this set of data d where each point => a + point.value * b
		/// </summary>
		/// <param name="a">Constant added.</param>
		/// <param name="b">Constant multiplied.</param>
		public SingleVariableDataSet LinearTransform (decimal a, decimal b)
		{
			return LinearTransform (this, a, b);
		}

		/// <summary>
		/// Adds the datapoint.
		/// </summary>
		/// <returns>The new dataset.</returns>
		/// <param name="d">D.</param>
		public SingleVariableDataSet AddData (DataPoint d)
		{
			var datanew = new List<DataPoint> (data);
			datanew.Add (d);
			return new SingleVariableDataSet (datanew);
		}

		/// <summary>
		/// Calculates the normal probability density function y = e ^ (-x^2/2) / sqrt(2pi)
		/// </summary>
		/// <returns>NormalPDF.</returns>
		/// <param name="value">Value.</param>
		public static double NormalPDF (double value)
		{
			return System.Math.Pow (System.Math.E, (-1d / 2)
			* System.Math.Pow (value, 2)) / System.Math.Sqrt (2 * System.Math.PI);
		}

		/// <summary>
		/// Calculates the NormalCDF, the probability that a random variable is less than the upper bound
		/// on the normal density distribution curve using Zelen and Severo's approximation (error &lt; 7.5*10^−8).
		/// </summary>
		/// <returns>Probability.</returns>
		/// <param name="upperBound">Upper bound (ZScore).</param>
		public static double NormalCDF (double upperBound)
		{
			//Bell's approximation (error &lt;= .0003)
			//return .5 * (1 + System.Math.Sign (upperBound) *
			//(1 - System.Math.Pow (System.Math.E, -2 / System.Math.PI * System.Math.Pow (upperBound, 2))));
			//Zelen and Severo's approximation (error &lt; 7.5*10^−8).
			if (upperBound < 0)//use symmetry to combat x > 0 requirement
				return ComplementNormalCDF (-upperBound);
			const double b0 = 0.2316419;
			const double b1 = 0.319381530;
			const double b2 = -0.356563782;
			const double b3 = 1.781477937;
			const double b4 = -1.821255978;
			const double b5 = 1.330274429;
			double PDF = NormalPDF (upperBound);
			double t = 1d / (1 + b0 * upperBound);
			return 1 - PDF * (b1 * t + b2 * t * t + b3 * t * t * t + b4 * t * t * t * t + b5 * t * t * t * t * t);
		}

		/// <summary>
		/// Calculates the complementary normalCDF, the probability that a random variable is greater than a lower
		/// bound on the normal density distribution curve using Zelen and Severo's approximation (error &lt; 7.5*10^−8).
		/// </summary>
		/// <returns>Probability.</returns>
		/// <param name="lowerBound">Lower bound (ZScore).</param>
		public static double ComplementNormalCDF (double lowerBound)
		{
			return 1 - NormalCDF (lowerBound);
		}

		/// <summary>
		/// Calculates the NormalCDF, the probability that a random variable is less than the upper bound
		/// and greater than the lower bound on the normal density distribution curve using 
		/// Zelen and Severo's approximation (error &lt; 7.5*10^−8).
		/// </summary>
		/// <returns>Probability.</returns>
		/// <param name="lowerBound">Lower bound (ZScore).</param>
		/// <param name="upperBound">Upper bound (ZScore).</param>
		public static double NormalCDF (double lowerBound, double upperBound)
		{
			if (lowerBound >= upperBound)
				throw new System.ArgumentException ($"{nameof (lowerBound)} >= {nameof (upperBound)}");
			return NormalCDF (upperBound) - NormalCDF (lowerBound);
		}

		/// <summary>
		/// Calculates the complementary normalCDF, the probability that a random variable is less than a lower
		/// bound  and greater than the upper bound on the normal density distribution curve using 
		/// Zelen and Severo's approximation (error &lt; 7.5*10^−8).
		/// </summary>
		/// <returns>Probability.</returns>
		/// <param name="lowerBound">Lower bound (ZScore).</param>
		/// <param name="upperBound">Upper bound (ZScore).</param>
		public static double ComplementNormalCDF (double lowerBound, double upperBound)
		{
			return 1 - NormalCDF (lowerBound, upperBound);
		}

		/// <summary>
		/// Calculates the NormalCDF, the probability that a random variable is less than the upper bound
		/// on the normal density distribution curve using Zelen and Severo's approximation
		///  (error &lt; 7.5*10^−8) and the given mean/standard deviation
		/// </summary>
		/// <returns>Probability.</returns>
		/// <param name="upperBound">Upper bound (non ZScore).</param>
		/// <param name = "mean">Mean</param>
		/// <param name = "standardDeviation">Standard Deviation</param>
		public static double NormalCDF (double upperBound, double mean, double standardDeviation)
		{
			return NormalCDF ((upperBound - mean) / standardDeviation);
		}

		/// <summary>
		/// Calculates the complementary normalCDF, the probability that a random variable is less than a lower
		/// bound on the normal density distribution curve using 
		/// Zelen and Severo's approximation (error &lt; 7.5*10^−8) and the given mean/standard deviation.
		/// </summary>
		/// <returns>The normal CD.</returns>
		/// <param name="lowerBound">Lower bound (non ZScore).</param>
		/// <param name="mean">Mean.</param>
		/// <param name="standardDeviation">Standard Deviation.</param>
		public static double ComplementNormalCDF (double lowerBound, double mean, double standardDeviation)
		{
			return 1 - NormalCDF (lowerBound, mean, standardDeviation);
		}

		/// <summary>
		/// Calculates the NormalCDF, the probability that a random variable is less than the upper bound
		/// and greater than the lower bound on the normal density distribution curve using 
		/// Zelen and Severo's approximation (error &lt; 7.5*10^−8) and the given mean/standard deviation.
		/// </summary>
		/// <returns>Probability.</returns>
		/// <param name="lowerBound">Lower bound (non ZScore).</param>
		/// <param name="upperBound">Upper bound (non ZScore).</param>
		/// <param name="mean">Mean.</param>
		/// <param name="standardDeviation">Standard Deviation.</param>
		public static double NormalCDF (double lowerBound, double upperBound, double mean, double standardDeviation)
		{
			upperBound = (upperBound - mean) / standardDeviation;
			lowerBound = (lowerBound - mean) / standardDeviation;
			return NormalCDF (lowerBound, upperBound);
		}

		/// <summary>
		/// Calculates the complementary normalCDF, the probability that a random variable is less than a lower
		/// bound  and greater than the upper bound on the normal density distribution curve using 
		/// Zelen and Severo's approximation (error &lt; 7.5*10^−8) and the given mean/standard deviation.
		/// </summary>
		/// <returns>The normal CD.</returns>
		/// <param name="lowerBound">Lower bound (non ZScore).</param>
		/// <param name="upperBound">Upper bound (non ZScore).</param>
		/// <param name="mean">Mean.</param>
		/// <param name="standardDeviation">Standard Deviation.</param>
		public static double ComplementNormalCDF (double lowerBound, double upperBound, double mean, double standardDeviation)
		{
			lowerBound = (lowerBound - mean) / standardDeviation;
			upperBound = (upperBound - mean) / standardDeviation;
			return ComplementNormalCDF (lowerBound, upperBound);
		}

		/// <summary>
		/// Calculates the inverse norm, or the Z-score a value must have to be greater than percentLeft of the data
		/// using the algorithm found at http://home.online.no/~pjacklam/notes/invnorm/#The_distribution_function
		/// (error &lt; 1.15 * 10^−9)
		/// </summary>
		/// <returns>The Z-score.</returns>
		/// <param name="percentLeft">Percent left.</param>
		public static double InverseNorm (double percentLeft)
		{
			const double P_LOW = 0.02425D;
			const double P_HIGH = 1.0D - P_LOW;

			// Coefficients in rational approximations.
			double[] ICDF_A = { -3.969683028665376e+01,  2.209460984245205e+02,
				-2.759285104469687e+02,  1.383577518672690e+02,
				-3.066479806614716e+01,  2.506628277459239e+00
			};

			double[] ICDF_B = { -5.447609879822406e+01,  1.615858368580409e+02,
				-1.556989798598866e+02,  6.680131188771972e+01,
				-1.328068155288572e+01
			};

			double[] ICDF_C = { -7.784894002430293e-03, -3.223964580411365e-01,
				-2.400758277161838e+00, -2.549732539343734e+00,
				4.374664141464968e+00,  2.938163982698783e+00
			};

			double[] ICDF_D = { 7.784695709041462e-03,  3.224671290700398e-01,
				2.445134137142996e+00,  3.754408661907416e+00
			};

			if (System.Math.Abs (percentLeft) < double.Epsilon)
				return double.NegativeInfinity;
			if (System.Math.Abs (percentLeft - 1) < double.Epsilon)
				return double.PositiveInfinity;
			if (double.IsNaN (percentLeft) || percentLeft < 0 || percentLeft > 1)
				throw new System.ArgumentException ($"{nameof (percentLeft)} must be in the closed interval [0,1]");
			if (percentLeft < P_LOW)
			{
				// Rational approximation for lower region:
				double q = System.Math.Sqrt (-2 * System.Math.Log (percentLeft));
				return (((((ICDF_C[0] * q + ICDF_C[1]) * q + ICDF_C[2]) * q + ICDF_C[3]) * q + ICDF_C[4]) * q + ICDF_C[5]) / ((((ICDF_D[0] * q + ICDF_D[1]) * q + ICDF_D[2]) * q + ICDF_D[3]) * q + 1);
			}
			if (P_HIGH < percentLeft)
			{
				// Rational approximation for upper region:
				double q = System.Math.Sqrt (-2 * System.Math.Log (1 - percentLeft));
				return -(((((ICDF_C[0] * q + ICDF_C[1]) * q + ICDF_C[2]) * q + ICDF_C[3]) * q + ICDF_C[4]) * q + ICDF_C[5]) / ((((ICDF_D[0] * q + ICDF_D[1]) * q + ICDF_D[2]) * q + ICDF_D[3]) * q + 1);
			}
			// Rational approximation for central region:
			double q2 = percentLeft - 0.5D;
			double r = q2 * q2;
			return (((((ICDF_A[0] * r + ICDF_A[1]) * r + ICDF_A[2]) * r + ICDF_A[3]) * r + ICDF_A[4]) * r + ICDF_A[5]) * q2 / (((((ICDF_B[0] * r + ICDF_B[1]) * r + ICDF_B[2]) * r + ICDF_B[3]) * r + ICDF_B[4]) * r + 1);
		}

		/// <summary>
		/// Calculates the inverse norm, or the value greater than percentLeft of the data
		/// using the algorithm found at http://home.online.no/~pjacklam/notes/invnorm/#The_distribution_function
		/// (error &lt; 1.15 * 10^−9) and the given mean/standard deviation.
		/// </summary>
		/// <returns>The value.</returns>
		/// <param name="percentLeft">Percent left.</param>
		/// <param name="mean">Mean.</param>
		/// <param name="standardDeviation">Standard Deviation.</param>
		public static double InverseNorm (double percentLeft, double mean, double standardDeviation)
		{
			return InverseNorm (percentLeft) * standardDeviation + mean;
		}

		/// <summary>
		/// Calculates the inverse norm, or the Z-score a value must have to be less than percentRight of the data
		/// using the algorithm found at http://home.online.no/~pjacklam/notes/invnorm/#The_distribution_function
		/// (error &lt; 1.15 * 10^−9)
		/// </summary>
		/// <returns>The Z-score.</returns>
		/// <param name="percentRight">Percent right.</param>
		public static double InverseNormRight (double percentRight)
		{
			return InverseNorm (1 - percentRight);
		}

		/// <summary>
		/// Calculates the inverse norm, or the value less than percentRight of the data
		/// using the algorithm found at http://home.online.no/~pjacklam/notes/invnorm/#The_distribution_function
		/// (error &lt; 1.15 * 10^−9) and the given mean/standard deviation.
		/// </summary>
		/// <returns>The Z-score.</returns>
		/// <param name="percentRight">Percent right.</param>
		/// <param name = "mean">Mean.</param>
		/// <param name = "standardDeviation">Standard deviation.</param>
		public static double InverseNormRight (double percentRight, double mean, double standardDeviation)
		{
			return InverseNormRight (percentRight) * standardDeviation + mean;
		}

		/// <summary>
		/// Normalize the specified d by computing z(x) = (x - mean) / standard deviation for each DataPoint x in d
		/// </summary>
		/// <param name="d">SingleVarirableDataSet.</param>
		public static SingleVariableDataSet Normalize (SingleVariableDataSet d)
		{
			var std = d.StandardDeviation ();
			return d.LinearTransform (-d.Mean () / (decimal)std, (decimal)(1 / std));
		}

		/// <summary>
		/// Normalize this instance by computing z(x) = (x - mean) / standard deviation for each DataPoint x in this
		/// </summary>
		public SingleVariableDataSet Normalize ()
		{
			return Normalize (this);
		}

		/// <summary>
		/// Gets the enumerator.
		/// </summary>
		/// <returns>The enumerator.</returns>
		public IEnumerator<DataPoint> GetEnumerator ()
		{
			foreach (DataPoint d in data)
			{
				yield return d;
			}
		}

		IEnumerator IEnumerable.GetEnumerator ()
		{
			return GetEnumerator ();
		}

		/// <summary>
		/// Copies the data to an array.
		/// </summary>
		/// <param name="array">Array.</param>
		/// <param name="index">Index.</param>
		public void CopyTo (System.Array array, int index)
		{
			data.ToArray ().CopyTo (array, index);
		}

		/// <summary>
		/// Gets the count.
		/// </summary>
		/// <value>The count.</value>
		public int Count
		{
			get
			{
				return data.Count;
			}
		}

		/// <summary>
		/// Gets the sync root.
		/// </summary>
		/// <value>The sync root.</value>
		public object SyncRoot
		{
			get;
		}

		/// <summary>
		/// Gets a value indicating whether this instance is synchronized.
		/// </summary>
		/// <value><c>true</c> if this instance is synchronized; otherwise, <c>false</c>.</value>
		public bool IsSynchronized
		{
			get
			{
				return false;
			}
		}

		/// <summary>
		/// Determines whether the specified <see cref="object"/> is equal to the current <see cref="SingleVariableDataSet"/>.
		/// </summary>
		/// <param name="obj">The <see cref="object"/> to compare with the current <see cref="SingleVariableDataSet"/>.</param>
		/// <returns><c>true</c> if the specified <see cref="object"/> is equal to the current
		/// <see cref="SingleVariableDataSet"/>; otherwise, <c>false</c>.</returns>
		public override bool Equals (object obj)
		{
			if (ReferenceEquals (obj, this))
				return true;
			if (obj == null)
				return false;
			var s = obj as SingleVariableDataSet;
			return s != null && s.data.Equals (data);
		}

		/// <summary>
		/// Serves as a hash function for a <see cref="SingleVariableDataSet"/> object.
		/// </summary>
		/// <returns>A hash code for this instance that is suitable for use in hashing algorithms and data structures such as a hash table.</returns>
		public override int GetHashCode ()
		{
			return new
			{
				data
			}.GetHashCode ();
		}

		/// <summary>
		/// Returns a <see cref="string"/> that represents the current <see cref="SingleVariableDataSet"/>.
		/// </summary>
		/// <returns>A <see cref="string"/> that represents the current <see cref="SingleVariableDataSet"/>.</returns>
		public override string ToString ()
		{
			return data.ToString ();
		}

		/// <summary>
		/// A Data point, or a wrapping type around a decimal.
		/// </summary>
		public struct DataPoint
		{
			/// <summary>
			/// Gets the value.
			/// </summary>
			/// <value>The value.</value>
			public decimal Value
			{
				get;
			}

			/// <summary>
			/// Initializes a new instance of the <see cref="DataPoint"/> struct.
			/// </summary>
			/// <param name="value">Value.</param>
			public DataPoint (decimal value)
			{
				Value = value;
			}

			/// <param name="s1">S1.</param>
			/// <param name="s2">S2.</param>
			public static bool operator == (DataPoint s1, DataPoint s2)
			{
				return s1.Value == s2.Value;
			}

			/// <param name="s1">S1.</param>
			/// <param name="s2">S2.</param>
			public static bool operator < (DataPoint s1, DataPoint s2)
			{
				return s1.Value < s2.Value;
			}

			/// <param name="s1">S1.</param>
			/// <param name="s2">S2.</param>
			public static bool operator > (DataPoint s1, DataPoint s2)
			{
				return s1.Value > s2.Value;
			}

			/// <param name="s1">S1.</param>
			/// <param name="s2">S2.</param>
			public static bool operator <= (DataPoint s1, DataPoint s2)
			{
				return s1.Value <= s2.Value;
			}

			/// <param name="s1">S1.</param>
			/// <param name="s2">S2.</param>
			public static bool operator >= (DataPoint s1, DataPoint s2)
			{
				return s1.Value >= s2.Value;
			}

			/// <param name="s1">S1.</param>
			/// <param name="s2">S2.</param>
			public static bool operator != (DataPoint s1, DataPoint s2)
			{
				return s1.Value != s2.Value;
			}

			/// <param name="s1">S1.</param>
			/// <param name="d">d</param>
			public static DataPoint operator + (DataPoint s1, decimal d)
			{
				return new DataPoint (s1.Value + d);
			}

			/// <param name="s">S.</param>
			public static DataPoint operator ++ (DataPoint s)
			{
				return s + 1;
			}

			/// <param name="s1">S1.</param>
			/// <param name="d">D.</param>
			public static DataPoint operator - (DataPoint s1, decimal d)
			{
				return new DataPoint (s1.Value - d);
			}

			/// <param name="s">S.</param>
			public static DataPoint operator -- (DataPoint s)
			{
				return s - 1;
			}

			/// <param name="s">S.</param>
			public static implicit operator decimal (DataPoint s)
			{
				return s.Value;
			}

			/// <summary>
			/// Determines whether the specified <see cref="object"/> is equal to the current <see cref="DataPoint"/>.
			/// </summary>
			/// <param name="obj">The <see cref="object"/> to compare with the current <see cref="DataPoint"/>.</param>
			/// <returns><c>true</c> if the specified <see cref="object"/> is equal to the current
			/// <see cref="DataPoint"/>; otherwise, <c>false</c>.</returns>
			public override bool Equals (object obj)
			{
				if (obj == null)
					return false;
				if (obj is DataPoint)
				{
					return (DataPoint)obj == this;
				}
				return false;
			}

			/// <summary>
			/// Serves as a hash function for a <see cref="DataPoint"/> object.
			/// </summary>
			/// <returns>A hash code for this instance that is suitable for use in hashing algorithms and data structures such as a hash table.</returns>
			public override int GetHashCode ()
			{
				return new
				{
					Value
				}.GetHashCode ();
			}
		}

		/// <summary>
		/// Interface describing the necessary methods a parser must implement to parse a string into
		/// a list of DataPoints.
		/// </summary>
		public interface IParser
		{
			/// <summary>
			/// Returns the list of data points
			/// </summary>
			/// <returns>The list.</returns>
			List<DataPoint> ToList ();

			/// <summary>
			/// Parses the string.
			/// </summary>
			/// <returns>The list of data points.</returns>
			/// <param name="data">Data.</param>
			List<DataPoint> ParseString (string data);
		}

		/// <summary>
		/// Default Parser class for parsing strings of data.
		/// Data should follow one of two formats:
		/// <para>[# #.# #.### ...]</para>
		/// <para>{# #.# #.### ...}</para>
		/// Separators can be either '.' or ','
		/// </summary>
		public class Parser : IParser
		{
			readonly List<DataPoint> datapoints;

			/// <summary>
			/// Initializes a new instance of the <see cref="Parser"/> class.
			/// </summary>
			public Parser ()
			{
				datapoints = new List<DataPoint> ();
			}

			/// <summary>
			/// Returns the list of data points
			/// </summary>
			/// <returns>The list.</returns>
			public List<DataPoint> ToList ()
			{
				return datapoints;
			}

			/// <summary>
			/// Parses the string.
			/// </summary>
			/// <returns>The list of data points.</returns>
			/// <param name="dataToParse">Data.</param>
			public List<DataPoint> ParseString (string dataToParse)
			{
				if (dataToParse == null)
					throw new System.ArgumentNullException (nameof (dataToParse));

				Parse (dataToParse);
				return ToList ();
			}

			void Parse (string dataToParse)
			{
				dataToParse = dataToParse.Trim ();
				if (dataToParse.StartsWith ("{", System.StringComparison.Ordinal) && dataToParse.EndsWith ("}", System.StringComparison.Ordinal))
				{
					ParseCurly (dataToParse);
				} else if (dataToParse.StartsWith ("[", System.StringComparison.Ordinal) && dataToParse.EndsWith ("]", System.StringComparison.Ordinal))
				{
					ParseSquare (dataToParse);
				} else
				{
					throw new System.ArgumentException ("Malformed data: " + dataToParse, $"{nameof (dataToParse)}");
				}
			}

			void ParseCurly (string dataToParse)
			{
				ParseList (dataToParse, '{', '}');
			}

			void ParseSquare (string dataToParse)
			{
				ParseList (dataToParse, '[', ']');
			}

			void ParseList (string dataToParse, char start, char end)
			{
				string[] parsed = dataToParse.Replace (',', '.').Replace (start, ' ').Replace (end, ' ').Trim ().Split (' ');
				foreach (string s in parsed)
				{
					if (!string.IsNullOrEmpty (s))
					{
						decimal test;
						if (decimal.TryParse (s, out test))
						{
							datapoints.Add (new DataPoint (test));
						} else
						{
							throw new System.ArgumentException ("Malformed data: " + s);
						}
					}
				}
			}
		}

		/// <summary>
		/// Empty data set exception.
		/// </summary>
		[System.Serializable]
		public class EmptyDataSetException : System.Exception
		{
			/// <summary>
			/// Initializes a new instance of the <see cref="EmptyDataSetException"/> class
			/// </summary>
			public EmptyDataSetException () : this ("DataSet Empty")
			{
			}

			/// <summary>
			/// Initializes a new instance of the <see cref="EmptyDataSetException"/> class
			/// </summary>
			/// <param name="message">A <see cref="T:System.String"/> that describes the exception. </param>
			public EmptyDataSetException (string message) : base (message)
			{
			}

			/// <summary>
			/// Initializes a new instance of the <see cref="EmptyDataSetException"/> class
			/// </summary>
			/// <param name="message">A <see cref="T:System.String"/> that describes the exception. </param>
			/// <param name="inner">The exception that is the cause of the current exception. </param>
			public EmptyDataSetException (string message, System.Exception inner) : base (message, inner)
			{
			}

			/// <summary>
			/// Initializes a new instance of the <see cref="EmptyDataSetException"/> class
			/// </summary>
			/// <param name="context">The contextual information about the source or destination.</param>
			/// <param name="info">The object that holds the serialized object data.</param>
			protected EmptyDataSetException (System.Runtime.Serialization.SerializationInfo info, System.Runtime.Serialization.StreamingContext context) : base (info, context)
			{
			}
		}
	}
}