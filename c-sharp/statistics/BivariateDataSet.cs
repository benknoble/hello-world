// //Ben Knoble's Project
using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace CollectionTypes
{
	/// <summary>
	/// Immutable collection of (X,Y) data points of quantitative data sorted by X value.
	/// </summary>
	public class BivariateDataSet : IEnumerable<BivariateDataSet.DataPoint>, ICollection
	{
		/// <summary>
		/// The X data.
		/// </summary>
		public readonly SingleVariableDataSet XData;
		/// <summary>
		/// The Y data.
		/// </summary>
		public readonly SingleVariableDataSet YData;

		readonly List<DataPoint> data;
		static readonly Dictionary<System.Predicate<double>, Strength> sDict = new Dictionary<System.Predicate<double>, Strength> {
			{ d => d >= .8, Strength.Strong },
			{ d => .6 <= d && d < .8, Strength.ModeratelyStrong },
			{ d => .4 <= d && d < .6, Strength.ModeratelyWeak },
			{ d => 0 <= d, Strength.Weak },
			{ d => true, Strength.Error }
		};

		/// <summary>
		/// Initializes a new instance of the <see cref="BivariateDataSet"/> class.
		/// </summary>
		/// <param name="data">Data.</param>
		public BivariateDataSet (List<DataPoint> data)
		{
			if (data.Count == 0)
				throw new EmptyDataSetException ($"{nameof (data)} is empty!");
			this.data = new List<DataPoint> (data);
			this.data = this.data.OrderBy (d => d.X).ToList ();
			XData = new SingleVariableDataSet (this.data.Select (d => new SingleVariableDataSet.DataPoint (d.X)).ToList ());
			YData = new SingleVariableDataSet (this.data.Select (d => new SingleVariableDataSet.DataPoint (d.Y)).ToList ());
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="BivariateDataSet"/> class.
		/// </summary>
		/// <param name="data">Data.</param>
		/// <param name="p">Parser for the string.</param>
		public BivariateDataSet (string data, IParser p)
		{
			this.data = new List<DataPoint> (p.ParseData (data));
			if (this.data.Count == 0)
				throw new EmptyDataSetException ($"{nameof (data)} contained no data points!");
			this.data = this.data.OrderBy (d => d.X).ToList ();
			XData = new SingleVariableDataSet (this.data.Select (d => new SingleVariableDataSet.DataPoint (d.X)).ToList ());
			YData = new SingleVariableDataSet (this.data.Select (d => new SingleVariableDataSet.DataPoint (d.Y)).ToList ());
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="BivariateDataSet"/> class.
		/// </summary>
		/// <param name="data">Data.</param>
		public BivariateDataSet (params DataPoint[] data)
		{
			if (data.Length == 0)
				throw new EmptyDataSetException ($"{nameof (data)} is empty!");
			this.data = data.ToList ();
			this.data = this.data.OrderBy (d => d.X).ToList ();
			XData = new SingleVariableDataSet (this.data.Select (d => new SingleVariableDataSet.DataPoint (d.X)).ToList ());
			YData = new SingleVariableDataSet (this.data.Select (d => new SingleVariableDataSet.DataPoint (d.Y)).ToList ());
		}

		BivariateDataSet ()
		{
		}

		/// <summary>
		/// Calculates r.
		/// </summary>
		public double R ()
		{
			double sum = 0;
			foreach (DataPoint d in data)
			{
				double x = XData.ZScore (new SingleVariableDataSet.DataPoint (d.X));
				double y = YData.ZScore (new SingleVariableDataSet.DataPoint (d.Y));
				sum += (x * y);
			}
			return sum / data.Count;
		}

		/// <summary>
		/// Calculates r^2
		/// </summary>
		public double RSquared ()
		{
			return System.Math.Pow (R (), 2);
		}

		/// <summary>
		/// Returns a description of the linear strength based on r.
		/// </summary>
		/// <returns>The strength.</returns>
		public Strength LinearStrength ()
		{
			double rAbs = System.Math.Abs (R ());
			foreach (var k in sDict.Keys)
			{
				if (k (rAbs))
				{
					return sDict[k];
				}
			}
			return Strength.Error;
		}

		/// <summary>
		/// Returns a least squares regression line y = a + b * x where b = r (Sy/Sx) and a = ybar - b * xbar
		/// </summary>
		/// <returns>The least squares regression line.</returns>
		public System.Func<decimal, DataPoint> LeastSquaresRegressionLine ()
		{
			var b = (decimal)(R () * YData.StandardDeviation () / XData.StandardDeviation ());
			decimal a = YData.Mean () - b * XData.Mean ();
			return x => new DataPoint (x, a + b * x);
		}

		/// <summary>
		/// Gets the enumerator.
		/// </summary>
		/// <returns>The enumerator.</returns>
		public IEnumerator<DataPoint> GetEnumerator ()
		{
			foreach (var d in data)
				yield return d;
		}

		IEnumerator IEnumerable.GetEnumerator ()
		{
			return GetEnumerator ();
		}

		/// <summary>
		/// Copies to array.
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
		/// Data point.
		/// </summary>
		public struct DataPoint
		{
			/// <summary>
			/// Gets the x.
			/// </summary>
			/// <value>The x.</value>
			public decimal X
			{
				get;
			}

			/// <summary>
			/// Gets the y.
			/// </summary>
			/// <value>The y.</value>
			public decimal Y
			{
				get;
			}

			/// <summary>
			/// Initializes a new instance of the <see cref="DataPoint"/> struct.
			/// </summary>
			/// <param name="x">The x coordinate.</param>
			/// <param name="y">The y coordinate.</param>
			public DataPoint (decimal x, decimal y)
			{
				X = x;
				Y = y;
			}
		}

		/// <summary>
		/// Strength.
		/// </summary>
		public enum Strength
		{
			/// <summary>
			/// r &gt;= .8
			/// </summary>
			Strong,
			/// <summary>
			/// .6 &lt;= r &lt; .8
			/// </summary>
			ModeratelyStrong,
			/// <summary>
			/// .4 &lt;= r &lt; .6
			/// </summary>
			ModeratelyWeak,
			/// <summary>
			/// 0 &lt;= r &lt; .4
			/// </summary>
			Weak,
			/// <summary>
			/// Error code.
			/// </summary>
			Error
		}

		/// <summary>
		/// Describes a parser capable of retrieving data from a string.
		/// </summary>
		public interface IParser
		{
			/// <summary>
			/// Returns a list of data points.
			/// </summary>
			/// <returns>The list.</returns>
			List<DataPoint> ToList ();

			/// <summary>
			/// Parses the data.
			/// </summary>
			/// <returns>The data.</returns>
			/// <param name="s">S.</param>
			List<DataPoint> ParseData (string s);
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