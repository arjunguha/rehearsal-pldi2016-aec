namespace $rootnamespace$.Controllers.Subscriptions
{
    using Core.Common.Subscriptions;
    using Extensions;
    using Filters;
    using Models;
	using System;
	using System.Web.Mvc;
    using Omu.ValueInjecter;

    public class SubscriptionController : Controller
    {
        [AllowAnonymous, FillDropDowns]
        public ActionResult Create()
        {
            return View(new CreditCardModel());
        }

        [HttpPost, AllowAnonymous, FillDropDowns]
        public ActionResult Create(CreditCardModel model)
        {
            if (ModelState.IsValid)
            {
                try
                {
                    var request = new AccountRequest();

                    request.InjectFrom<UnflatLoopValueInjection>(this.GetCurrentUser(), model);                    

                    var response = SubscriptionsManager.CreateAccount(request);
                }
                catch (Exception ex)
                {
                    ModelState.AddModelError("", ex.Message);
                }
  

            }
            return View(model);
        }

    }
}
