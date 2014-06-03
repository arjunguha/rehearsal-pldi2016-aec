namespace $rootnamespace$.Controllers.Home
{
    using System.Web.Mvc;

    public partial class HomeController
    {
        [HttpGet]
        public ActionResult Start()
        {
            return RedirectToAction("Index", "Dashboard");
        }
    }
}
