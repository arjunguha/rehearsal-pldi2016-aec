namespace $rootnamespace$.Controllers.Fulfillment
{
    using System.Web.Mvc;

    public partial class FulfillmentController : Controller
    {
		public ActionResult Manager()
        {
            return this.View();
        }      
    }
}