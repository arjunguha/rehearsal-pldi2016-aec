using System.Web.Mvc;

namespace $rootnamespace$.Controllers.Offers
{
    using $rootnamespace$.Core.Model;

    public class OffersController : Controller
    {
        public ActionResult Record()
        {
            return this.View();
        }

		public ActionResult Manager()
        {
            return this.View();
        }
    }
}
