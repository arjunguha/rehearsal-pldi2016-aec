namespace $rootnamespace$.Controllers.Account
{
    using System.Web.Mvc;
    using Core.Common.Membership;
    using Core.Common.Membership.Events;
    using Core.Infrastructure.Eventing;
    using Core.Model;
    using Extensions;
    using Models;

    public partial class AccountController
    {
        [AllowAnonymous]
        public ActionResult Logon()
        {
            return View(new LogOnModel());
        }

        [HttpPost]
        [AllowAnonymous]
        public ActionResult Logon(LogOnModel model, string returnUrl)
        {
            if (ModelState.IsValid)
            {
                User user;
                var status = _userService.Authenticate(model.UserName, model.Password, out user);

                switch (status)
                {
                    case AuthenticationStatus.Authenticated:

                        _authenticationService.SetAuthCookie(model.UserName, model.RememberMe);

                        MessageBus.Instance.Publish(new UserLoggedIn(user));

                        string redirectUrl = _authenticationService.GetRedirectUrl(model.UserName, false);
                        
                        return Redirect(redirectUrl);

                    case AuthenticationStatus.UserLockedOut:

                        ModelState.AddModelError(string.Empty, "The account is currently locked");
                        break;

                    case AuthenticationStatus.AccountNotActive:

                        ModelState.AddModelError(string.Empty, "The account is no longer active");
                        break;

                    case AuthenticationStatus.ResetPassword:

                        _authenticationService.SetAuthCookie(model.UserName, model.RememberMe);

                        TempData["Error"] = "Password Change Required";
                        
                        return RedirectToAction("ChangePassword", "Account", new { username = model.UserName });

                    default:

                        ModelState.AddModelError(string.Empty, "The username or password provided is incorrect");
                        break;
                }
            }

            return View(model);
        }

        public ActionResult LogOff()
        {
            MessageBus.Instance.Publish(new UserLoggedOut(this.GetCurrentUser()));

            _authenticationService.SignOut();            
            return RedirectToAction("Index", "Home");
        }       
    }
}