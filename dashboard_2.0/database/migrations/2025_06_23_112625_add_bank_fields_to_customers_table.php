<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if (Schema::hasTable('customers')) {
            Schema::table('customers', function (Blueprint $table) {
                $table->string('account_holder_name')->nullable();
                $table->string('ifsc_code')->nullable();
                $table->string('account_no')->nullable();
                $table->string('bank_name')->nullable();
                $table->string('bank_city')->nullable();
                $table->string('bank_branch')->nullable();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasTable('customers')) {
            Schema::table('customers', function (Blueprint $table) {
                $table->dropColumn([
                    'account_holder_name',
                    'ifsc_code',
                    'account_no',
                    'bank_name',
                    'bank_city',
                    'bank_branch',
                ]);
            });
        }
    }
};
